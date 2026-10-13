#!/usr/bin/env python3
"""Локальный архив почтового ящика по IMAP.

    python3 mail_archive.py              # скачать все письма (.eml), затем предложит собрать HTML
    python3 mail_archive.py render       # собрать HTML-страницы и вложения из уже скачанных .eml
    python3 mail_archive.py pack         # сжать архив в один файл .tar.xz
    python3 mail_archive.py unpack       # развернуть .tar.xz обратно в каталог
    python3 mail_archive.py delete       # удалить с сервера письма, у которых есть локальная копия

Все команды, кроме delete, ящик только читают: папки открываются в режиме
read-only, на сервере ничего не удаляется и не помечается прочитанным.
Повторный запуск download докачивает недостающее.

Структура архива:
    archive/index.html                  список папок
    archive/<папка>/index.html          список писем с поиском
    archive/<папка>/eml/<uid>.eml       оригинал письма (точная копия с сервера)
    archive/<папка>/html/<uid>.html     письмо для просмотра в браузере
    archive/<папка>/files/<uid>/...     вложения
"""
from __future__ import annotations

import argparse
import atexit
import base64
import collections
import getpass
import html
import imaplib
import json
import lzma
import mimetypes
import os
import re
import select
import shutil
import signal
import sys
import tarfile
import threading
import time
from email import message_from_binary_file, policy
from email.utils import parsedate_to_datetime
from pathlib import Path
from urllib.parse import quote, unquote

try:
    import termios
    import tty
except ImportError:  # не Unix: управление клавишами недоступно, остаётся Ctrl+C
    termios = tty = None

TIMEOUT = 120  # секунд на одну сетевую операцию
RETRIES = 5  # попыток на одно письмо
MAX_FAILS_IN_ROW = 3  # столько писем подряд не скачалось — считаем, что связи нет
DELETE_BATCH = 100  # писем за одну команду удаления; между пачками срабатывают пауза и остановка
CONFIRM_WORD = "удалить"
NET_ERRORS = (imaplib.IMAP4.error, OSError, EOFError)
TTY = sys.stdout.isatty()
KEYS_HINT = "Управление: p или пробел — пауза/продолжить, q или Ctrl+C — остановить."


# ---------------------------------------------------------------- утилиты

def fmt_size(n: float) -> str:
    for unit in ("Б", "КБ", "МБ", "ГБ"):
        if abs(n) < 1024 or unit == "ГБ":
            return f"{n:.0f} {unit}" if unit == "Б" else f"{n:.1f} {unit}"
        n /= 1024
    return ""


def fmt_time(sec: float) -> str:
    sec = int(sec)
    return f"{sec // 3600:02d}:{sec % 3600 // 60:02d}:{sec % 60:02d}"


def safe_name(name: str, fallback: str = "_") -> str:
    name = re.sub(r'[\x00-\x1f/\\:*?"<>|]', "_", name).strip().lstrip(".")
    stem, ext = os.path.splitext(name)
    return (stem[:80] + ext[:20]) or fallback


def decode_utf7(s: str) -> str:
    """Имена папок IMAP приходят в modified UTF-7 (RFC 3501)."""
    def repl(m):
        b = m.group(1)
        if not b:
            return "&"
        try:
            return base64.b64decode(b.replace(",", "/") + "=" * (-len(b) % 4)).decode("utf-16-be")
        except Exception:
            return m.group(0)
    return re.sub(r"&([^-]*)-", repl, s)


def read_json(path: Path, default=None):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return default


def write_json(path: Path, data) -> None:
    tmp = path.with_name(path.name + ".part")
    tmp.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
    os.replace(tmp, path)


def ask(prompt: str, default: str = "") -> str:
    answer = input(prompt).strip()
    return answer or default


def ask_yes(prompt: str, default: bool = True) -> bool:
    answer = ask(f"{prompt} [{'Y/n' if default else 'y/N'}] ").lower()
    if not answer:
        return default
    return answer[0] in ("y", "д")


# ---------------------------------------------------------------- пауза / отмена

class Controls:
    """Клавиши p/пробел (пауза) и q (отмена) без Enter; Ctrl+C — мягкая отмена."""

    def __init__(self):
        self.paused = threading.Event()
        self.cancelled = threading.Event()
        self._fd = None
        self._old_term = None
        self._old_sigint = None
        self._stop = threading.Event()

    def __enter__(self):
        self._stop.clear()
        self._old_sigint = signal.signal(signal.SIGINT, self._on_sigint)
        if termios and sys.stdin.isatty():
            self._fd = sys.stdin.fileno()
            self._old_term = termios.tcgetattr(self._fd)
            tty.setcbreak(self._fd)
            atexit.register(self._restore)
            threading.Thread(target=self._read_keys, daemon=True).start()
        return self

    def __exit__(self, *exc):
        self._stop.set()
        self._restore()
        signal.signal(signal.SIGINT, self._old_sigint)

    def _restore(self):
        if self._old_term is not None:
            termios.tcsetattr(self._fd, termios.TCSADRAIN, self._old_term)
            self._old_term = None

    def _on_sigint(self, signum, frame):
        if self.cancelled.is_set():  # второй Ctrl+C — выходим немедленно
            raise KeyboardInterrupt
        self.cancelled.set()

    def _read_keys(self):
        while not self._stop.is_set():
            try:
                ready, _, _ = select.select([self._fd], [], [], 0.2)
                if not ready:
                    continue
                ch = os.read(self._fd, 8).decode("utf-8", "ignore").lower()
            except (OSError, ValueError):
                return
            # «з» и «й» — те же клавиши p и q в русской раскладке
            if ch in ("p", "з", " "):
                if self.paused.is_set():
                    self.paused.clear()
                else:
                    self.paused.set()
            elif ch in ("q", "й"):
                self.cancelled.set()

    def checkpoint(self, tick=None, idle=None) -> bool:
        """Ждёт, пока стоит пауза. Возвращает False, если работу отменили."""
        last_idle = time.monotonic()
        while self.paused.is_set() and not self.cancelled.is_set():
            if tick:
                tick()
            time.sleep(0.2)
            if idle and time.monotonic() - last_idle > 60:
                idle()
                last_idle = time.monotonic()
        return not self.cancelled.is_set()


# ---------------------------------------------------------------- прогресс

class Progress:
    def __init__(self, total_items: int, total_bytes: int, controls: Controls):
        self.total_items = total_items
        self.total_bytes = total_bytes
        self.controls = controls
        self.items = 0
        self.bytes = 0
        self.label = ""
        self._samples = collections.deque()  # (время, байт) за последние секунды — для скорости
        self._last_draw = 0.0

    def advance(self, nbytes: int, items: int = 1) -> None:
        self.items += items
        self.bytes += nbytes
        self._samples.append((time.monotonic(), self.bytes))
        self.draw()

    def _speed(self) -> float:
        now = time.monotonic()
        while self._samples and now - self._samples[0][0] > 15:
            self._samples.popleft()
        if len(self._samples) < 2:
            return 0.0
        (t0, b0), (t1, b1) = self._samples[0], self._samples[-1]
        return (b1 - b0) / (t1 - t0) if t1 > t0 else 0.0

    def draw(self, force: bool = False) -> None:
        now = time.monotonic()
        if not force and now - self._last_draw < (0.1 if TTY else 5):
            return
        self._last_draw = now
        if self.total_bytes:
            frac = self.bytes / self.total_bytes
        else:
            frac = self.items / self.total_items if self.total_items else 1.0
        frac = min(frac, 1.0)
        if self.controls.paused.is_set():
            self._samples.clear()
            state = "ПАУЗА (p — продолжить)"
        else:
            speed = self._speed()
            eta = fmt_time((self.total_bytes - self.bytes) / speed) if speed > 0 else "--:--:--"
            state = f"{fmt_size(speed)}/с  осталось {eta}"
        filled = int(frac * 24)
        line = (f"[{'#' * filled}{'.' * (24 - filled)}] {frac * 100:5.1f}%  "
                f"{self.items}{f'/{self.total_items}' if self.total_items else ''}  "
                f"{fmt_size(self.bytes)}/{fmt_size(self.total_bytes)}  {state}  {self.label}")
        if TTY:
            width = shutil.get_terminal_size().columns
            sys.stdout.write("\r\033[K" + line[:width - 1])
            sys.stdout.flush()
        else:
            print(line, flush=True)

    def log(self, msg: str) -> None:
        if TTY:
            sys.stdout.write("\r\033[K")
        print(msg, flush=True)
        self.draw(force=True)

    def finish(self) -> None:
        self.draw(force=True)
        if TTY:
            print()


# ---------------------------------------------------------------- IMAP

LIST_RE = re.compile(rb'\((?P<flags>[^)]*)\)\s+(?P<delim>"(?:\\.|[^"])*"|NIL)\s*(?P<name>.*)$', re.S)


class Mailbox:
    def __init__(self, cfg: dict, password: str):
        self.cfg = cfg
        self.password = password
        self.conn = None

    def connect(self) -> None:
        self.close()
        host, port = self.cfg["host"], self.cfg["port"]
        if self.cfg.get("starttls"):
            conn = imaplib.IMAP4(host, port, timeout=TIMEOUT)
            conn.starttls()
        else:
            conn = imaplib.IMAP4_SSL(host, port, timeout=TIMEOUT)
        conn.login(self.cfg["user"], self.password)
        self.conn = conn

    def close(self) -> None:
        if self.conn is not None:
            try:
                self.conn.shutdown()
            except Exception:
                pass
            self.conn = None

    def noop(self) -> None:
        try:
            self.conn.noop()
        except Exception:
            pass  # обрыв обнаружится и починится на следующем письме

    def list_folders(self) -> list:
        typ, data = self.conn.list()
        if typ != "OK":
            raise imaplib.IMAP4.error(f"LIST: {data}")
        folders = []
        for item in data:
            if isinstance(item, tuple):  # имя пришло литералом
                head, name = item[0], item[1]
            else:
                head, name = item, None
            m = LIST_RE.match(head or b"")
            if not m:
                continue
            if name is None:
                name = m.group("name").strip()
                if name.startswith(b'"') and name.endswith(b'"'):
                    name = re.sub(rb"\\(.)", rb"\1", name[1:-1])
            flags = m.group("flags").decode("ascii", "replace").lower()
            if not name or "\\noselect" in flags or "\\nonexistent" in flags:
                continue
            raw = name.decode("utf-8", "replace")
            folders.append({"raw": raw, "name": decode_utf7(raw)})
        return folders

    def select(self, raw: str, readonly: bool = True) -> tuple:
        quoted = '"' + raw.replace("\\", "\\\\").replace('"', '\\"') + '"'
        typ, data = self.conn.select(quoted, readonly=readonly)
        if typ != "OK":
            raise imaplib.IMAP4.error(f"SELECT {raw}: {data}")
        count = int(data[0] or 0)
        uidvalidity = self.conn.response("UIDVALIDITY")[1][0]
        return count, (uidvalidity or b"0").decode()

    def scan(self) -> dict:
        """uid -> {size, flags, date} для всех писем выбранной папки."""
        typ, data = self.conn.fetch("1:*", "(UID RFC822.SIZE FLAGS INTERNALDATE)")
        if typ != "OK":
            raise imaplib.IMAP4.error(f"FETCH: {data}")
        messages = {}
        for item in data:
            line = item[0] if isinstance(item, tuple) else item
            if not line:
                continue
            uid = re.search(rb"UID (\d+)", line)
            size = re.search(rb"RFC822\.SIZE (\d+)", line)
            if not uid:
                continue
            flags = re.search(rb"FLAGS \(([^)]*)\)", line)
            date = re.search(rb'INTERNALDATE "([^"]+)"', line)
            messages[uid.group(1).decode()] = {
                "size": int(size.group(1)) if size else 0,
                "flags": flags.group(1).decode("ascii", "replace") if flags else "",
                "date": date.group(1).decode("ascii", "replace") if date else "",
            }
        return messages

    def fetch(self, uid: str):
        typ, data = self.conn.uid("FETCH", uid, "(BODY.PEEK[])")
        if typ != "OK":
            raise imaplib.IMAP4.error(f"FETCH {uid}: {data}")
        for item in data:
            if isinstance(item, tuple) and len(item) >= 2:
                return item[1]
        return None  # письма уже нет на сервере


def with_retry(mbox: Mailbox, raw_folder: str, fn, progress: Progress, controls: Controls,
               readonly: bool = True):
    delay = 2
    for attempt in range(1, RETRIES + 1):
        try:
            return fn()
        except NET_ERRORS as e:
            if attempt == RETRIES or controls.cancelled.is_set():
                raise
            progress.log(f"  ошибка связи ({e}); переподключение через {delay} с "
                         f"(попытка {attempt + 1}/{RETRIES})")
            controls.cancelled.wait(delay)
            delay = min(delay * 2, 60)
            try:
                mbox.connect()
                mbox.select(raw_folder, readonly)
            except NET_ERRORS:
                pass


# ---------------------------------------------------------------- скачивание

def load_config(root: Path, args) -> dict:
    cfg = read_json(root / "config.json", {}) or {}
    if args.host:
        cfg["host"] = args.host
    if args.user:
        cfg["user"] = args.user
    if args.starttls:
        cfg["starttls"] = True
    if args.port:
        cfg["port"] = args.port
    if not cfg.get("host"):
        cfg["host"] = ask("IMAP-сервер [mail.bmstu.ru]: ", "mail.bmstu.ru")
    if not cfg.get("user"):
        cfg["user"] = ask("Логин (обычно полный адрес почты): ")
    cfg.setdefault("port", 143 if cfg.get("starttls") else 993)
    return cfg


def open_mailbox(cfg: dict) -> Mailbox:
    password = os.environ.get("MAIL_PASSWORD") or getpass.getpass(f"Пароль для {cfg['user']}: ")
    mbox = Mailbox(cfg, password)
    print(f"Подключение к {cfg['host']}:{cfg['port']}…")
    try:
        mbox.connect()
    except imaplib.IMAP4.error as e:
        sys.exit(f"Не удалось войти: {e}")
    except OSError as e:
        sys.exit(f"Не удалось подключиться: {e}")
    return mbox


def folder_dir(root: Path, folder: dict, uidvalidity: str) -> Path:
    """Каталог папки. При смене UIDVALIDITY старая копия откладывается в сторону."""
    base = safe_name(folder["name"].replace("/", "."), "folder")
    n = 1
    while True:
        path = root / (base if n == 1 else f"{base}_{n}")
        info = read_json(path / "folder.json")
        if info is None or info.get("raw") == folder["raw"]:
            break
        n += 1
    if info and info.get("uidvalidity") != uidvalidity:
        stale = path.with_name(f"{path.name}.stale-{info.get('uidvalidity')}")
        print(f"  ! у папки сменился UIDVALIDITY, прежняя копия перенесена в {stale.name}")
        os.rename(path, stale)
    (path / "eml").mkdir(parents=True, exist_ok=True)
    write_json(path / "folder.json", {"name": folder["name"], "raw": folder["raw"],
                                      "uidvalidity": uidvalidity})
    return path


def parse_selection(text: str, count: int) -> list:
    chosen = set()
    for part in text.replace(" ", "").split(","):
        if not part:
            continue
        lo, _, hi = part.partition("-")
        for i in range(int(lo), int(hi or lo) + 1):
            if 1 <= i <= count:
                chosen.add(i - 1)
    return sorted(chosen)


def set_mtime(path: Path, internaldate: str) -> None:
    try:
        parsed = imaplib.Internaldate2tuple(b'INTERNALDATE "' + internaldate.encode() + b'"')
        ts = time.mktime(parsed)
        os.utime(path, (ts, ts))
    except Exception:
        pass


def cmd_download(root: Path, args) -> bool:
    """Возвращает True, если скачивание дошло до конца без отмены."""
    root.mkdir(parents=True, exist_ok=True)
    cfg = load_config(root, args)
    mbox = open_mailbox(cfg)
    write_json(root / "config.json", cfg)

    print("Сканирование папок…")
    plan = []
    for folder in mbox.list_folders():
        try:
            count, uidvalidity = mbox.select(folder["raw"])
            messages = mbox.scan() if count else {}
        except imaplib.IMAP4.error as e:
            print(f"  ! {folder['name']}: пропущена ({e})")
            continue
        path = folder_dir(root, folder, uidvalidity)
        write_json(path / "messages.json", messages)
        todo = [uid for uid in sorted(messages, key=int) if not (path / "eml" / f"{uid}.eml").exists()]
        plan.append({"folder": folder, "path": path, "messages": messages, "todo": todo})

    if not plan:
        print("Папок не найдено.")
        return False
    print(f"\n{'№':>3}  {'писем':>7}  {'размер':>10}  {'осталось':>8}  {'докачать':>10}  папка")
    for i, p in enumerate(plan, 1):
        total = sum(m["size"] for m in p["messages"].values())
        left = sum(p["messages"][uid]["size"] for uid in p["todo"])
        print(f"{i:>3}  {len(p['messages']):>7}  {fmt_size(total):>10}  {len(p['todo']):>8}  "
              f"{fmt_size(left):>10}  {p['folder']['name']}")

    answer = ask("\nКакие папки качать? [Enter — все, либо номера: 1,3-5] ")
    try:
        selected = [plan[i] for i in parse_selection(answer, len(plan))] if answer else plan
    except ValueError:
        sys.exit("Не понял список номеров.")
    total_items = sum(len(p["todo"]) for p in selected)
    total_bytes = sum(p["messages"][uid]["size"] for p in selected for uid in p["todo"])
    if not total_items:
        print("Всё уже скачано.")
        summary(selected, [])
        mbox.close()
        return True
    free = shutil.disk_usage(root).free
    print(f"К скачиванию: {total_items} писем, {fmt_size(total_bytes)}. "
          f"Свободно на диске: {fmt_size(free)}.")
    if total_bytes * 1.1 > free and not ask_yes("Места может не хватить. Продолжить?", False):
        return False
    if not ask_yes("Начать?"):
        return False

    print(KEYS_HINT)
    failed = []
    fails_in_row = 0
    aborted = False
    controls = Controls()
    progress = Progress(total_items, total_bytes, controls)
    with controls:
        for p in selected:
            if not p["todo"] or aborted or controls.cancelled.is_set():
                continue
            raw, name = p["folder"]["raw"], p["folder"]["name"]
            progress.label = name
            try:
                with_retry(mbox, raw, lambda: mbox.select(raw), progress, controls)
            except NET_ERRORS as e:
                progress.log(f"  ! {name}: не удалось открыть папку ({e})")
                failed.extend((name, uid) for uid in p["todo"])
                continue
            for uid in p["todo"]:
                if not controls.checkpoint(tick=progress.draw, idle=mbox.noop):
                    break
                size = p["messages"][uid]["size"]
                try:
                    body = with_retry(mbox, raw, lambda: mbox.fetch(uid), progress, controls)
                except NET_ERRORS as e:
                    if controls.cancelled.is_set():
                        break
                    progress.log(f"  ! {name} / письмо {uid}: не скачано ({e})")
                    failed.append((name, uid))
                    fails_in_row += 1
                    if fails_in_row >= MAX_FAILS_IN_ROW:
                        progress.log("Несколько ошибок подряд — похоже, нет связи. Останавливаюсь.")
                        aborted = True
                        break
                    continue
                fails_in_row = 0
                if body:
                    target = p["path"] / "eml" / f"{uid}.eml"
                    tmp = target.with_name(target.name + ".part")
                    tmp.write_bytes(body)
                    os.replace(tmp, target)
                    set_mtime(target, p["messages"][uid]["date"])
                else:
                    progress.log(f"  ! {name} / письмо {uid}: сервер его не отдал (удалено?)")
                    failed.append((name, uid))
                progress.advance(size)
        progress.finish()
    mbox.close()

    stopped = controls.cancelled.is_set() or aborted
    if stopped:
        print("Остановлено. Запустите скрипт ещё раз — он продолжит с того же места.")
    summary(selected, failed)
    return not stopped


def summary(selected: list, failed: list) -> None:
    print(f"\n{'на сервере':>10}  {'локально':>8}  папка")
    all_ok = True
    for p in selected:
        local = sum(1 for uid in p["messages"] if (p["path"] / "eml" / f"{uid}.eml").exists())
        ok = local == len(p["messages"])
        all_ok = all_ok and ok
        print(f"{len(p['messages']):>10}  {local:>8}  {'✓' if ok else '✗'} {p['folder']['name']}")
    if failed:
        print(f"Не скачано писем: {len(failed)}")
    if all_ok:
        print("Все письма выбранных папок сохранены локально.")
    else:
        print("Копия НЕПОЛНАЯ — не удаляйте письма с сервера, пока везде не будет ✓.")


# ---------------------------------------------------------------- удаление с сервера

def has_copy(path: Path, uid: str) -> bool:
    try:
        return (path / "eml" / f"{uid}.eml").stat().st_size > 0
    except OSError:
        return False


def check(response) -> None:
    typ, data = response
    if typ != "OK":
        raise imaplib.IMAP4.error(f"{typ}: {data}")


def cmd_delete(root: Path) -> None:
    """Удаляет с сервера только те письма, для которых есть непустой локальный .eml."""
    cfg = read_json(root / "config.json")
    if not cfg:
        sys.exit(f"В {root} нет архива. Сначала скачайте почту: python3 mail_archive.py")
    copies = {}  # (имя папки на сервере, UIDVALIDITY) -> каталог с локальной копией
    for info_file in root.glob("*/folder.json"):
        info = read_json(info_file)
        if info:
            copies[(info.get("raw"), info.get("uidvalidity"))] = info_file.parent

    mbox = open_mailbox(cfg)
    try:
        uidplus = "UIDPLUS" in mbox.conn.capability()[1][0].decode("ascii", "replace").upper().split()
    except Exception:
        uidplus = False

    print("Сверка сервера с локальным архивом…")
    plan = []
    for folder in mbox.list_folders():
        try:
            count, uidvalidity = mbox.select(folder["raw"])
            messages = mbox.scan() if count else {}
        except imaplib.IMAP4.error as e:
            print(f"  ! {folder['name']}: пропущена ({e})")
            continue
        path = copies.get((folder["raw"], uidvalidity))
        backed = sorted((uid for uid in messages if path and has_copy(path, uid)), key=int)
        backed_set = set(backed)
        # письма, уже помеченные удалёнными, но без локальной копии: обычный EXPUNGE стёр бы и их
        stray = any("\\deleted" in m["flags"].lower()
                    for uid, m in messages.items() if uid not in backed_set)
        plan.append({"folder": folder, "messages": messages, "backed": backed, "stray": stray,
                     "has_dir": path is not None})

    if not plan:
        sys.exit("Папок не найдено.")
    print(f"\n{'№':>3}  {'на сервере':>10}  {'удалить':>8}  {'останется':>9}  {'освободится':>11}  папка")
    for i, p in enumerate(plan, 1):
        freed = sum(p["messages"][uid]["size"] for uid in p["backed"])
        note = "" if p["has_dir"] or not p["messages"] else "  (нет локальной копии)"
        print(f"{i:>3}  {len(p['messages']):>10}  {len(p['backed']):>8}  "
              f"{len(p['messages']) - len(p['backed']):>9}  {fmt_size(freed):>11}  "
              f"{p['folder']['name']}{note}")
    print("«Останется» — письма без локальной копии, они не удаляются.")

    answer = ask("\nВ каких папках удалять? [Enter — во всех, либо номера: 1,3-5] ")
    try:
        selected = [plan[i] for i in parse_selection(answer, len(plan))] if answer else plan
    except ValueError:
        sys.exit("Не понял список номеров.")
    selected = [p for p in selected if p["backed"]]
    total_items = sum(len(p["backed"]) for p in selected)
    total_bytes = sum(p["messages"][uid]["size"] for p in selected for uid in p["backed"])
    if not total_items:
        print("Удалять нечего.")
        return

    print(f"\nБудет БЕЗВОЗВРАТНО удалено с сервера: {total_items} писем, {fmt_size(total_bytes)}, "
          f"папок: {len(selected)}.")
    print("Письма стираются сразу, мимо корзины; восстановить их с сервера будет нельзя.")
    print(f"Единственным экземпляром останется архив {root} —")
    print("убедитесь, что он открывается и что у него есть вторая копия.")
    if ask(f"Для подтверждения введите слово «{CONFIRM_WORD}»: ").lower() != CONFIRM_WORD:
        print("Отменено, ничего не удалено.")
        return

    print(KEYS_HINT)
    failed = 0
    controls = Controls()
    progress = Progress(total_items, total_bytes, controls)
    with controls:
        for p in selected:
            if controls.cancelled.is_set():
                break
            raw, name = p["folder"]["raw"], p["folder"]["name"]
            progress.label = name
            expunge = uidplus or not p["stray"]
            if not expunge:
                progress.log(f"  ! {name}: в папке есть ранее помеченные удалёнными письма без "
                             "локальной копии. Письма будут только помечены удалёнными — "
                             "окончательно очистите папку вручную.")
            try:
                with_retry(mbox, raw, lambda: mbox.select(raw, readonly=False), progress, controls,
                           readonly=False)
            except NET_ERRORS as e:
                progress.log(f"  ! {name}: не удалось открыть папку на запись ({e})")
                failed += len(p["backed"])
                continue
            for i in range(0, len(p["backed"]), DELETE_BATCH):
                if not controls.checkpoint(tick=progress.draw, idle=mbox.noop):
                    break
                batch = p["backed"][i:i + DELETE_BATCH]
                uidset = ",".join(batch)

                def delete_batch():
                    check(mbox.conn.uid("STORE", uidset, "+FLAGS.SILENT", "(\\Deleted)"))
                    if uidplus:
                        check(mbox.conn.uid("EXPUNGE", uidset))
                    elif expunge:
                        check(mbox.conn.expunge())

                try:
                    with_retry(mbox, raw, delete_batch, progress, controls, readonly=False)
                except NET_ERRORS as e:
                    if not controls.cancelled.is_set():
                        progress.log(f"  ! {name}: удаление прервано ({e})")
                        failed += len(p["backed"]) - i
                    break
                progress.advance(sum(p["messages"][uid]["size"] for uid in batch), len(batch))
        progress.finish()

    if controls.cancelled.is_set():
        print("Остановлено. Уже удалённые письма не вернутся; остальные на месте.")
    if failed:
        print(f"Не удалось удалить писем: {failed}. Запустите команду ещё раз.")
    print(f"\n{'было':>8}  {'осталось':>8}  папка")
    for p in selected:
        try:
            left = mbox.select(p["folder"]["raw"])[0]
        except NET_ERRORS:
            left = "?"
        print(f"{len(p['messages']):>8}  {left:>8}  {p['folder']['name']}")
    mbox.close()
    print("Если квота не уменьшилась, проверьте корзину и настройки хранения в веб-интерфейсе почты.")


# ---------------------------------------------------------------- сжатие

def is_derived(rel: Path) -> bool:
    """HTML-страницы, вложения и списки — всё, что команда render восстановит из .eml."""
    return ((len(rel.parts) >= 2 and rel.parts[1] in ("html", "files"))
            or rel.name in ("index.html", "index.json"))


def cmd_pack(root: Path, target: Path, full: bool, level: int) -> None:
    if not root.is_dir():
        sys.exit(f"Каталог {root} не найден.")
    files = []
    for path in sorted(root.rglob("*")):
        if not path.is_file() or path.name.endswith(".part"):
            continue
        rel = path.relative_to(root)
        if full or not is_derived(rel):
            files.append((path, rel, path.stat().st_size))
    if not files:
        sys.exit(f"В {root} нечего сжимать.")
    total_bytes = sum(size for _, _, size in files)
    if target.exists() and not ask_yes(f"{target} уже существует. Перезаписать?", False):
        return
    what = "весь каталог" if full else "оригиналы писем (.eml) и служебные файлы"
    print(f"Сжатие: {what}, {len(files)} файлов, {fmt_size(total_bytes)} → {target}")
    print("Сильное сжатие работает медленно: на несколько гигабайт уходит час и больше.")
    print(KEYS_HINT)

    tmp = target.with_name(target.name + ".part")
    controls = Controls()
    progress = Progress(len(files), total_bytes, controls)
    try:
        with controls, lzma.open(tmp, "wb", preset=level) as xz, \
                tarfile.open(fileobj=xz, mode="w") as tar:
            for path, rel, size in files:
                if not controls.checkpoint(tick=progress.draw):
                    break
                progress.label = rel.parts[0]
                tar.add(path, arcname=rel.as_posix(), recursive=False)
                progress.advance(size)
            progress.finish()
    except BaseException:
        tmp.unlink(missing_ok=True)
        raise
    if controls.cancelled.is_set():
        tmp.unlink(missing_ok=True)
        print("Остановлено, недописанный файл удалён.")
        return
    os.replace(tmp, target)
    packed = target.stat().st_size
    print(f"Готово: {fmt_size(total_bytes)} → {fmt_size(packed)} "
          f"({packed / total_bytes * 100:.0f}% от исходного)." if total_bytes else "Готово.")
    if not full:
        print("HTML-страницы и вложения в файл не входят — после распаковки их соберёт render.")


def cmd_unpack(root: Path, source: Path) -> bool:
    """Возвращает True, если распаковка дошла до конца."""
    if not source.is_file():
        sys.exit(f"Файл {source} не найден.")
    if root.exists() and any(root.iterdir()) and not ask_yes(
            f"Каталог {root} не пуст; файлы с совпадающими именами будут перезаписаны. Продолжить?",
            False):
        return False
    root.mkdir(parents=True, exist_ok=True)
    print(f"Распаковка {source} → {root}")
    print(KEYS_HINT)
    controls = Controls()
    progress = Progress(0, source.stat().st_size, controls)  # прогресс — по прочитанному из файла
    with controls, open(source, "rb") as raw, lzma.open(raw) as xz, \
            tarfile.open(fileobj=xz, mode="r|") as tar:
        for member in tar:
            if not controls.checkpoint(tick=progress.draw):
                break
            target = (root / member.name).resolve()
            if not member.isfile() or root not in target.parents:
                continue  # в архиве могут быть только обычные файлы внутри каталога
            progress.label = Path(member.name).parts[0]
            target.parent.mkdir(parents=True, exist_ok=True)
            tmp = target.with_name(target.name + ".part")
            with tar.extractfile(member) as src, open(tmp, "wb") as dst:
                shutil.copyfileobj(src, dst)
            os.replace(tmp, target)
            os.utime(target, (member.mtime, member.mtime))
            progress.advance(raw.tell() - progress.bytes)
        progress.finish()
    if controls.cancelled.is_set():
        print("Остановлено. Запустите unpack ещё раз, чтобы распаковать заново.")
        return False
    print(f"Распаковано файлов: {progress.items}.")
    return True


# ---------------------------------------------------------------- HTML

CSS = """
:root{color-scheme:light dark}
body{font:15px/1.45 -apple-system,system-ui,sans-serif;margin:0 auto;padding:16px;max-width:1200px}
a{color:#06c}h1{font-size:20px;margin:12px 0}
table{border-collapse:collapse;width:100%}
td,th{padding:4px 10px 4px 0;text-align:left;vertical-align:top}
.list td,.list th{border-bottom:1px solid #8884}
.list td:first-child,.num{white-space:nowrap}
.hdr th{width:1%;white-space:nowrap;font-weight:normal;opacity:.65}
.att{padding:8px 0}.att a{display:inline-block;margin-right:14px}
input{font:inherit;padding:6px 10px;width:100%;box-sizing:border-box;margin:8px 0}
iframe{width:100%;height:80vh;border:1px solid #8884;background:#fff;margin-top:8px}
pre{white-space:pre-wrap;word-wrap:break-word;font:14px/1.45 ui-monospace,Menlo,monospace}
"""

FIT_JS = """
const f=document.querySelector('iframe');
function fit(){try{f.style.height=f.contentDocument.documentElement.scrollHeight+24+'px'}catch(e){}}
if(f){f.addEventListener('load',fit);setTimeout(fit,300)}
"""

FILTER_JS = """
const q=document.getElementById('q'),rows=[...document.querySelectorAll('tbody tr')];
q.addEventListener('input',()=>{const s=q.value.toLowerCase();
for(const r of rows)r.hidden=!r.textContent.toLowerCase().includes(s)});
"""


def page(title: str, body: str, script: str = "") -> str:
    return (f'<!doctype html><html lang="ru"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1">'
            f"<title>{html.escape(title)}</title><style>{CSS}</style></head><body>{body}"
            f"<script>{script}</script></body></html>")


def hdr(msg, name: str) -> str:
    try:
        return str(msg[name] or "").strip()
    except Exception:
        return ""


def part_text(part) -> str:
    try:
        return part.get_content()
    except Exception:
        return (part.get_payload(decode=True) or b"").decode("utf-8", "replace")


def render_message(folder_path: Path, folder_name: str, uid: str) -> dict:
    eml = folder_path / "eml" / f"{uid}.eml"
    with open(eml, "rb") as f:
        msg = message_from_binary_file(f, policy=policy.default)

    try:
        dt = parsedate_to_datetime(hdr(msg, "date")).astimezone()
        ts = dt.timestamp()
    except Exception:
        ts = eml.stat().st_mtime
    date = time.strftime("%Y-%m-%d %H:%M", time.localtime(ts))
    subject = hdr(msg, "subject") or "(без темы)"

    bodies = {}
    for kind in ("html", "plain"):
        try:
            bodies[kind] = msg.get_body(preferencelist=(kind,))
        except Exception:
            bodies[kind] = None
    body = bodies["html"] or bodies["plain"]
    skip = {id(b) for b in bodies.values() if b is not None}

    files_dir = folder_path / "files" / uid
    attachments = []  # (имя файла, размер)
    cids = {}
    n = 0
    for part in msg.walk():
        if part.is_multipart() or id(part) in skip:
            continue
        n += 1
        try:
            filename = part.get_filename()
        except Exception:
            filename = None
        if not filename:
            ext = mimetypes.guess_extension(part.get_content_type()) or ".bin"
            filename = f"part{n}{ext}"
        filename = safe_name(str(filename), f"part{n}")
        stem, ext = os.path.splitext(filename)
        taken = {a[0] for a in attachments}
        k = 1
        while filename in taken:
            k += 1
            filename = f"{stem}_{k}{ext}"
        try:
            data = part.get_payload(decode=True) or b""
        except Exception:
            data = b""
        files_dir.mkdir(parents=True, exist_ok=True)
        (files_dir / filename).write_bytes(data)
        attachments.append((filename, len(data)))
        cid = hdr(part, "content-id").strip("<>")
        if cid:
            cids[cid] = f"../files/{uid}/{quote(filename)}"

    if body is None:
        content = "<p>(нет текста)</p>"
    elif body.get_content_type() == "text/html":
        text = re.sub(r"cid:([^\"'\s>)]+)",
                      lambda m: cids.get(unquote(m.group(1)), m.group(0)), part_text(body))
        # sandbox без allow-scripts: скрипты из письма не выполняются
        content = ('<iframe sandbox="allow-same-origin allow-popups allow-popups-to-escape-sandbox" '
                   f'srcdoc="{html.escape("<base target=_blank>" + text, quote=True)}"></iframe>')
    else:
        content = f"<pre>{html.escape(part_text(body))}</pre>"

    rows = "".join(
        f"<tr><th>{label}</th><td>{html.escape(value)}</td></tr>"
        for label, value in (("От", hdr(msg, "from")), ("Кому", hdr(msg, "to")),
                             ("Копия", hdr(msg, "cc")), ("Дата", date)) if value)
    links = "".join(
        f'<a href="../files/{uid}/{quote(name)}">📎 {html.escape(name)} ({fmt_size(size)})</a>'
        for name, size in attachments)
    out = (f'<p><a href="../index.html">← {html.escape(folder_name)}</a></p>'
           f"<h1>{html.escape(subject)}</h1><table class=hdr>{rows}</table>"
           f'<div class=att>{links}<a href="../eml/{uid}.eml">Оригинал (.eml)</a></div>{content}')
    html_dir = folder_path / "html"
    html_dir.mkdir(exist_ok=True)
    (html_dir / f"{uid}.html").write_text(page(subject, out, FIT_JS), encoding="utf-8",
                                          errors="replace")
    return {"ts": ts, "date": date, "from": hdr(msg, "from"), "to": hdr(msg, "to"),
            "subject": subject, "att": len(attachments), "size": eml.stat().st_size}


def write_folder_index(path: Path, name: str, cache: dict) -> None:
    rows = []
    for uid, m in sorted(cache.items(), key=lambda kv: kv[1]["ts"], reverse=True):
        rows.append(
            f"<tr><td>{m['date']}</td><td>{html.escape(m['from'])}</td>"
            f"<td>{html.escape(m['to'])}</td>"
            f'<td><a href="html/{uid}.html">{html.escape(m["subject"])}</a></td>'
            f"<td class=num>{'📎' + str(m['att']) if m['att'] else ''}</td>"
            f"<td class=num>{fmt_size(m['size'])}</td></tr>")
    body = (f'<p><a href="../index.html">← Все папки</a></p><h1>{html.escape(name)} '
            f"({len(cache)})</h1><input id=q placeholder='Поиск по списку…' autofocus>"
            "<table class=list><thead><tr><th>Дата</th><th>От</th><th>Кому</th><th>Тема</th>"
            f"<th></th><th>Размер</th></tr></thead><tbody>{''.join(rows)}</tbody></table>")
    (path / "index.html").write_text(page(name, body, FILTER_JS), encoding="utf-8",
                                     errors="replace")


def cmd_render(root: Path, force: bool) -> None:
    folders = []
    for info_file in sorted(root.glob("*/folder.json")):
        path = info_file.parent
        info = read_json(info_file, {}) or {}
        cache = {} if force else (read_json(path / "index.json", {}) or {})
        uids = sorted((p.stem for p in (path / "eml").glob("*.eml")), key=int)
        cache = {uid: m for uid, m in cache.items() if uid in set(uids)}
        todo = [uid for uid in uids
                if uid not in cache or not (path / "html" / f"{uid}.html").exists()]
        folders.append({"path": path, "name": info.get("name", path.name),
                        "cache": cache, "todo": todo})
    if not folders:
        print(f"В {root} нет скачанных папок.")
        return

    total_items = sum(len(f["todo"]) for f in folders)
    total_bytes = sum((f["path"] / "eml" / f"{uid}.eml").stat().st_size
                      for f in folders for uid in f["todo"])
    errors = 0
    controls = Controls()
    if total_items:
        print(f"Сборка HTML: {total_items} писем, {fmt_size(total_bytes)}.")
        print(KEYS_HINT)
        progress = Progress(total_items, total_bytes, controls)
        with controls:
            for f in folders:
                progress.label = f["name"]
                for uid in f["todo"]:
                    if not controls.checkpoint(tick=progress.draw):
                        break
                    size = (f["path"] / "eml" / f"{uid}.eml").stat().st_size
                    try:
                        f["cache"][uid] = render_message(f["path"], f["name"], uid)
                    except Exception as e:
                        errors += 1
                        progress.log(f"  ! {f['name']} / письмо {uid}: {e!r}")
                    progress.advance(size)
                if controls.cancelled.is_set():
                    break
            progress.finish()

    rows = []
    for f in folders:
        write_json(f["path"] / "index.json", f["cache"])
        write_folder_index(f["path"], f["name"], f["cache"])
        size = sum(m["size"] for m in f["cache"].values())
        rows.append(f'<tr><td><a href="{quote(f["path"].name)}/index.html">'
                    f"{html.escape(f['name'])}</a></td><td class=num>{len(f['cache'])}</td>"
                    f"<td class=num>{fmt_size(size)}</td></tr>")
    body = ("<h1>Архив почты</h1><table class=list><thead><tr><th>Папка</th><th>Писем</th>"
            f"<th>Размер</th></tr></thead><tbody>{''.join(rows)}</tbody></table>")
    (root / "index.html").write_text(page("Архив почты", body), encoding="utf-8")

    if controls.cancelled.is_set():
        print("Остановлено. Запустите render ещё раз, чтобы продолжить.")
    if errors:
        print(f"Не удалось обработать писем: {errors} (их .eml на месте).")
    print(f"Откройте в браузере: {root / 'index.html'}")


# ---------------------------------------------------------------- запуск

def main() -> None:
    if sys.version_info < (3, 9):
        sys.exit("Нужен Python 3.9 или новее.")
    parser = argparse.ArgumentParser(description="Локальный архив почтового ящика по IMAP.")
    parser.add_argument("command", nargs="?", default="download",
                        choices=["download", "render", "pack", "unpack", "delete"],
                        help="download — скачать письма (по умолчанию); render — собрать HTML "
                             "из скачанного; pack / unpack — сжать архив в файл и развернуть "
                             "обратно; delete — удалить с сервера письма, сохранённые локально")
    parser.add_argument("--dir", default="archive", help="каталог архива (по умолчанию ./archive)")
    parser.add_argument("--host", help="IMAP-сервер")
    parser.add_argument("--port", type=int, help="порт (по умолчанию 993, для --starttls 143)")
    parser.add_argument("--user", help="логин")
    parser.add_argument("--starttls", action="store_true", help="STARTTLS вместо SSL")
    parser.add_argument("--force", action="store_true", help="render: пересобрать все страницы")
    parser.add_argument("--file", help="pack/unpack: файл архива (по умолчанию <каталог>.tar.xz)")
    parser.add_argument("--full", action="store_true",
                        help="pack: сжать и HTML с вложениями, а не только оригиналы писем")
    parser.add_argument("--level", type=int, default=9, choices=range(10), metavar="0-9",
                        help="pack: степень сжатия (по умолчанию 9 — максимальная)")
    args = parser.parse_args()
    root = Path(args.dir).resolve()
    packed = Path(args.file).resolve() if args.file else root.with_name(root.name + ".tar.xz")

    if args.command == "render":
        cmd_render(root, args.force)
    elif args.command == "delete":
        cmd_delete(root)
    elif args.command == "pack":
        cmd_pack(root, packed, args.full, args.level)
    elif args.command == "unpack":
        if (cmd_unpack(root, packed) and not (root / "index.html").exists()
                and ask_yes("\nСобрать HTML-страницы сейчас?")):
            cmd_render(root, args.force)
    elif cmd_download(root, args) and ask_yes("\nСобрать HTML-страницы сейчас?"):
        cmd_render(root, args.force)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nПрервано.")
        sys.exit(130)
