#!/usr/bin/env python3
"""
Telegram Bot v3.1 — Archivador en la Nube
Pyrogram + MTProto | Archivos hasta 2 GB
"""

import os
import asyncio
import logging
import shutil
import re
import json
import subprocess
import mimetypes
import time
import uuid
import hmac
import hashlib
import base64
import secrets as _secrets
from pathlib import Path
from urllib.parse import urlparse, unquote, quote
from datetime import date, datetime, timedelta

# ─── Compatibilidad Python 3.10+ / 3.14 (Pyrogram requiere event loop al importar) ──
try:
    _loop = asyncio.get_event_loop()
    if _loop.is_closed():
        raise RuntimeError("closed")
except RuntimeError:
    asyncio.set_event_loop(asyncio.new_event_loop())

from dotenv import load_dotenv
load_dotenv()

import aiohttp
from aiohttp import web as aioweb
import aiofiles
import aiosqlite
import internetarchive as ia

try:
    import py7zr
    _PY7ZR_AVAILABLE = True
except ImportError:
    _PY7ZR_AVAILABLE = False

from pyrogram import Client, filters, idle, enums
from pyrogram.types import (
    Message,
    InlineKeyboardMarkup,
    InlineKeyboardButton,
    CallbackQuery,
    BotCommand,
    BotCommandScopeDefault,
    BotCommandScopeChat,
)

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)

# ─── Configuración ─────────────────────────────────────────────────────────────

def _safe_int(value: str, default: int = 0) -> int:
    try:
        return int(str(value).strip())
    except (ValueError, TypeError):
        return default


BOT_TOKEN          = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
API_ID             = _safe_int(os.environ.get("TELEGRAM_API_ID", "0"))
API_HASH           = os.environ.get("TELEGRAM_API_HASH", "").strip()
_ADMIN_RAW         = os.environ.get("TELEGRAM_ADMIN_ID", "").strip().lstrip("@")
_raw_contact = os.environ.get("TELEGRAM_ADMIN_USERNAME", "").strip()
if _raw_contact.startswith("https://t.me/"):
    _raw_contact = _raw_contact[len("https://t.me/"):]
elif _raw_contact.startswith("t.me/"):
    _raw_contact = _raw_contact[len("t.me/"):]
_ADMIN_CONTACT_RAW = _raw_contact.lstrip("@")
ARCHIVE_ACCESS     = os.environ.get("ARCHIVE_ORG_ACCESS_KEY", "").strip()
ARCHIVE_SECRET     = os.environ.get("ARCHIVE_ORG_SECRET_KEY", "").strip()

_ADMIN_ID: int | None = None
_ADMIN_USERNAME: str | None = None
if _ADMIN_RAW.lstrip("-").isdigit():
    _ADMIN_ID = int(_ADMIN_RAW)
elif _ADMIN_RAW:
    _ADMIN_USERNAME = _ADMIN_RAW.lower()

USERS_FILE    = Path("users.json")
DB_FILE       = Path("bot_data.db")
TEMP_DIR      = Path("temp_downloads")
TEMP_DIR.mkdir(exist_ok=True)
HEALTH_PORT   = _safe_int(os.environ.get("PORT", "8080"), 8080)

DEFAULT_QUOTA = 10
PM = enums.ParseMode.HTML

# ─── Servidor de Almacenamiento Local (sin gastar MB en Cuba) ─────────────────
#
# Si el usuario coloca este servidor detrás de una pasarela cubana (proxy
# nacional, dominio .cu, CDN del usuario, etc.) las descargas no descontarán
# datos del paquete de internet de ETECSA.
#
# Variables relevantes:
#   STORAGE_PUBLIC_URL   URL pública con la que se construyen los enlaces.
#                        Si no se define, intenta RENDER_EXTERNAL_URL y luego
#                        http://localhost:PORT.
#   STORAGE_TOKEN_SECRET Secreto HMAC para firmar enlaces.
#                        Si no se define, se deriva del BOT_TOKEN.
#   STORAGE_MAX_GB       Capacidad máxima en GB del servidor (auto-purga).
#   STORAGE_FILE_TTL_DAYS  Días que vive cada archivo (0 = para siempre).
#
# Rate-limit por usuario para el botón "Pedir aprobación" (uid → epoch)
_ACCESS_REQ_COOLDOWN: dict[int, float] = {}

STORAGE_DIR = Path("storage_files")
STORAGE_DIR.mkdir(exist_ok=True)

STORAGE_PUBLIC_URL = (
    os.environ.get("STORAGE_PUBLIC_URL", "").strip().rstrip("/")
    or os.environ.get("RENDER_EXTERNAL_URL", "").strip().rstrip("/")
    or f"http://localhost:{HEALTH_PORT}"
)

_secret_seed = (
    os.environ.get("STORAGE_TOKEN_SECRET", "").strip()
    or BOT_TOKEN
    or "fallback-storage-secret-change-me"
)
STORAGE_TOKEN_SECRET = hashlib.sha256(_secret_seed.encode()).digest()

STORAGE_MAX_GB        = _safe_int(os.environ.get("STORAGE_MAX_GB", "10"), 10)
STORAGE_FILE_TTL_DAYS = _safe_int(os.environ.get("STORAGE_FILE_TTL_DAYS", "0"), 0)

# Tamaño de chunk para servir archivos (256 KB · óptimo para conexiones móviles)
STORAGE_SERVE_CHUNK = 256 * 1024

# Lista de URLs alternativas (mirrors) donde también está disponible el archivo.
# Útil para colocar un proxy/mirror dentro de Cuba que no descuenta MB de ETECSA.
# Formato: "https://cuba.dominio.cu, https://otro-mirror.example".
STORAGE_MIRRORS: list[str] = [
    u.strip().rstrip("/")
    for u in os.environ.get("STORAGE_MIRRORS", "").split(",")
    if u.strip()
]

# Destino de subida por defecto: "archive" (archive.org) o "local" (servidor propio)
DEFAULT_UPLOAD_DEST = os.environ.get("DEFAULT_UPLOAD_DEST", "archive").strip().lower()
if DEFAULT_UPLOAD_DEST not in ("archive", "local"):
    DEFAULT_UPLOAD_DEST = "archive"

# ─── Estado global ─────────────────────────────────────────────────────────────

job_queues:       dict[int, asyncio.Queue] = {}
active_tasks:     dict[int, dict]          = {}
pending_quality:  dict[str, dict]          = {}
pending_playlist: dict[str, dict]          = {}
pending_dm_search: dict[str, dict]         = {}

DM_PER_PAGE = 5

# ─── Contacto admin ────────────────────────────────────────────────────────────

def admin_contact_url() -> str:
    if _ADMIN_CONTACT_RAW:
        return f"https://t.me/{_ADMIN_CONTACT_RAW}"
    if _ADMIN_USERNAME:
        return f"https://t.me/{_ADMIN_USERNAME}"
    return "https://t.me"


def admin_contact_btn(requester_uid: int | None = None) -> InlineKeyboardMarkup:
    """Devuelve los botones para usuarios sin acceso.

    Si se pasa `requester_uid`, añade un botón que dispara una solicitud
    de aprobación que llega al chat del admin con el bot (no solo al
    perfil de Telegram del admin)."""
    rows = []
    if requester_uid is not None:
        rows.append([
            InlineKeyboardButton(
                "🔔 Pedir aprobación al admin",
                callback_data=f"req_access_{requester_uid}",
            )
        ])
    rows.append([
        InlineKeyboardButton("📩 Contactar Administrador", url=admin_contact_url())
    ])
    return InlineKeyboardMarkup(rows)

# ─── Utilidades de texto ───────────────────────────────────────────────────────

def bi(text: str) -> str:
    result = []
    for ch in text:
        if "A" <= ch <= "Z":
            result.append(chr(0x1D63C + ord(ch) - ord("A")))
        elif "a" <= ch <= "z":
            result.append(chr(0x1D656 + ord(ch) - ord("a")))
        elif "0" <= ch <= "9":
            result.append(chr(0x1D7EC + ord(ch) - ord("0")))
        else:
            result.append(ch)
    return "".join(result)


def esc(text: str) -> str:
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def fmt_size(size_bytes: int) -> str:
    if size_bytes < 1024:
        return f"{size_bytes} B"
    elif size_bytes < 1024 ** 2:
        return f"{size_bytes / 1024:.1f} KB"
    elif size_bytes < 1024 ** 3:
        return f"{size_bytes / 1024 ** 2:.1f} MB"
    else:
        return f"{size_bytes / 1024 ** 3:.2f} GB"


def fmt_eta(seconds: float) -> str:
    if seconds < 0 or seconds > 86400:
        return "—"
    elif seconds < 60:
        return f"{int(seconds)}s"
    elif seconds < 3600:
        return f"{int(seconds // 60)}m {int(seconds % 60)}s"
    else:
        return f"{int(seconds // 3600)}h {int((seconds % 3600) // 60)}m"


def progress_bar(pct: float, width: int = 18) -> str:
    filled = int(width * pct / 100)
    return "█" * filled + "░" * (width - filled)


def sanitize_name(name: str) -> str:
    name = re.sub(r"[^\w\s\-.]", "", name)
    name = name.strip().replace(" ", "_")
    return name[:80] if name else "archivo"


# ─── Gestión de usuarios ───────────────────────────────────────────────────────

def _admin_matches(uid: int, uname: str | None) -> bool:
    if _ADMIN_ID is not None and uid == _ADMIN_ID:
        return True
    if _ADMIN_USERNAME and uname and uname.lower() == _ADMIN_USERNAME:
        return True
    return False


def load_users() -> dict:
    if USERS_FILE.exists():
        try:
            with open(USERS_FILE, "r") as f:
                data = json.load(f)
            data.setdefault("allowed", [])
            data.setdefault("banned", [])
            return data
        except Exception:
            pass
    initial: list = []
    if _ADMIN_ID:
        initial.append(_ADMIN_ID)
    if _ADMIN_USERNAME:
        initial.append(_ADMIN_USERNAME)
    return {"allowed": initial, "banned": []}


def save_users(data: dict):
    with open(USERS_FILE, "w") as f:
        json.dump(data, f, indent=2)


def _in_list(lst: list, uid: int, uname: str | None) -> bool:
    if uid in lst:
        return True
    if uname and uname.lower() in [str(x).lower() for x in lst]:
        return True
    return False


def is_admin(uid: int, uname: str | None = None) -> bool:
    return _admin_matches(uid, uname)


def is_allowed(uid: int, uname: str | None = None) -> bool:
    if _admin_matches(uid, uname):
        return True
    data = load_users()
    return _in_list(data["allowed"], uid, uname) and not _in_list(data["banned"], uid, uname)


def is_banned(uid: int, uname: str | None = None) -> bool:
    return _in_list(load_users()["banned"], uid, uname)


# ─── Base de datos ─────────────────────────────────────────────────────────────

async def init_db():
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute("""
            CREATE TABLE IF NOT EXISTS upload_history (
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id    INTEGER NOT NULL,
                username   TEXT,
                first_name TEXT,
                filename   TEXT,
                link       TEXT,
                size       INTEGER DEFAULT 0,
                created_at TEXT DEFAULT (datetime('now', 'localtime'))
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS daily_usage (
                user_id INTEGER,
                date    TEXT,
                count   INTEGER DEFAULT 0,
                PRIMARY KEY (user_id, date)
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS user_quota (
                user_id     INTEGER PRIMARY KEY,
                daily_limit INTEGER DEFAULT 10
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS settings (
                key   TEXT PRIMARY KEY,
                value TEXT
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS storage_files (
                identifier TEXT PRIMARY KEY,
                filename   TEXT NOT NULL,
                size       INTEGER DEFAULT 0,
                user_id    INTEGER,
                created_at TEXT DEFAULT (datetime('now', 'localtime')),
                sha256     TEXT
            )
        """)
        # Migración: añade la columna sha256 a tablas existentes.
        try:
            await db.execute("ALTER TABLE storage_files ADD COLUMN sha256 TEXT")
        except Exception:
            pass  # ya existe
        await db.commit()


# ─── Settings (clave/valor) ────────────────────────────────────────────────────

async def get_setting(key: str, default: str = "") -> str:
    async with aiosqlite.connect(DB_FILE) as db:
        async with db.execute("SELECT value FROM settings WHERE key=?", (key,)) as cur:
            row = await cur.fetchone()
            return row[0] if row else default


async def set_setting(key: str, value: str):
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute(
            "INSERT INTO settings (key, value) VALUES (?, ?) "
            "ON CONFLICT(key) DO UPDATE SET value=?",
            (key, value, value),
        )
        await db.commit()


async def get_upload_dest() -> str:
    val = await get_setting("upload_dest", DEFAULT_UPLOAD_DEST)
    return val if val in ("archive", "local") else DEFAULT_UPLOAD_DEST


async def set_upload_dest(dest: str):
    if dest not in ("archive", "local"):
        raise ValueError("Destino inválido")
    await set_setting("upload_dest", dest)


# ─── Catálogo del servidor de almacenamiento ──────────────────────────────────

async def register_storage_file(identifier: str, filename: str, size: int, user_id: int):
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute(
            "INSERT OR REPLACE INTO storage_files "
            "(identifier, filename, size, user_id) VALUES (?, ?, ?, ?)",
            (identifier, filename, size, user_id),
        )
        await db.commit()


async def list_storage_files() -> list:
    async with aiosqlite.connect(DB_FILE) as db:
        async with db.execute(
            "SELECT identifier, filename, size, created_at FROM storage_files "
            "ORDER BY created_at DESC"
        ) as cur:
            return await cur.fetchall()


async def delete_storage_file(identifier: str) -> bool:
    folder = STORAGE_DIR / identifier
    removed = False
    if folder.exists():
        shutil.rmtree(folder, ignore_errors=True)
        removed = True
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute("DELETE FROM storage_files WHERE identifier=?", (identifier,))
        await db.commit()
    return removed


async def get_storage_sha256(identifier: str) -> str | None:
    """Devuelve el sha256 cacheado del archivo, o None si aún no se calculó."""
    async with aiosqlite.connect(DB_FILE) as db:
        async with db.execute(
            "SELECT sha256 FROM storage_files WHERE identifier=?", (identifier,),
        ) as cur:
            row = await cur.fetchone()
            return row[0] if row and row[0] else None


async def set_storage_sha256(identifier: str, sha256_hex: str):
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute(
            "UPDATE storage_files SET sha256=? WHERE identifier=?",
            (sha256_hex, identifier),
        )
        await db.commit()


async def compute_storage_sha256(identifier: str, file_path: Path):
    """Calcula sha256 en background y lo guarda en la BD.

    Permite que los clientes (gestores de descarga, navegadores que soporten
    Digest, scripts) verifiquen integridad de descargas reanudadas SIN
    reenviar el archivo entero — esencial para no malgastar MB en Cuba."""
    if not file_path.exists():
        return
    try:
        loop = asyncio.get_running_loop()
        def _hash() -> str:
            h = hashlib.sha256()
            with open(file_path, "rb") as f:
                while True:
                    chunk = f.read(1024 * 1024)  # 1 MB
                    if not chunk:
                        break
                    h.update(chunk)
            return h.hexdigest()
        digest = await loop.run_in_executor(None, _hash)
        await set_storage_sha256(identifier, digest)
        logger.info(f"Storage: sha256 calculado para {identifier} ({digest[:12]}...)")
    except Exception as e:
        logger.warning(f"Storage: no se pudo calcular sha256 de {identifier}: {e}")


async def get_daily_usage(uid: int) -> int:
    today = date.today().isoformat()
    async with aiosqlite.connect(DB_FILE) as db:
        async with db.execute(
            "SELECT count FROM daily_usage WHERE user_id=? AND date=?", (uid, today)
        ) as cur:
            row = await cur.fetchone()
            return row[0] if row else 0


async def get_quota(uid: int) -> int:
    async with aiosqlite.connect(DB_FILE) as db:
        async with db.execute(
            "SELECT daily_limit FROM user_quota WHERE user_id=?", (uid,)
        ) as cur:
            row = await cur.fetchone()
            return row[0] if row else DEFAULT_QUOTA


async def set_quota(uid: int, limit: int):
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute(
            "INSERT INTO user_quota (user_id, daily_limit) VALUES (?, ?) "
            "ON CONFLICT(user_id) DO UPDATE SET daily_limit=?",
            (uid, limit, limit),
        )
        await db.commit()


async def increment_usage(uid: int):
    today = date.today().isoformat()
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute(
            "INSERT INTO daily_usage (user_id, date, count) VALUES (?, ?, 1) "
            "ON CONFLICT(user_id, date) DO UPDATE SET count = count + 1",
            (uid, today),
        )
        await db.commit()


async def add_history(uid: int, uname: str | None, fname: str, filename: str, link: str, size: int):
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute(
            "INSERT INTO upload_history (user_id, username, first_name, filename, link, size) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (uid, uname or "", fname, filename, link, size),
        )
        await db.commit()


async def get_history(uid: int, limit: int = 10) -> list:
    async with aiosqlite.connect(DB_FILE) as db:
        async with db.execute(
            "SELECT filename, link, size, created_at FROM upload_history "
            "WHERE user_id=? ORDER BY id DESC LIMIT ?",
            (uid, limit),
        ) as cur:
            return await cur.fetchall()


# ─── Detección de URLs ─────────────────────────────────────────────────────────

PLATFORM_PATTERNS = [
    r"(?:https?://)?(?:www\.)?youtube\.com/",
    r"(?:https?://)?youtu\.be/",
    r"(?:https?://)?(?:www\.)?instagram\.com/",
    r"(?:https?://)?(?:vm\.)?tiktok\.com/",
    r"(?:https?://)?(?:www\.)?tiktok\.com/",
    r"(?:https?://)?(?:www\.)?twitter\.com/",
    r"(?:https?://)?(?:www\.)?x\.com/",
    r"(?:https?://)?(?:www\.)?dailymotion\.com/",
    r"(?:https?://)?dai\.ly/",
]


def is_platform_url(url: str) -> bool:
    return any(re.search(p, url, re.IGNORECASE) for p in PLATFORM_PATTERNS)


def is_youtube_playlist(url: str) -> bool:
    return (
        bool(re.search(r"(?:list=|/playlist\?)", url, re.IGNORECASE))
        and bool(re.search(r"youtube\.com|youtu\.be", url, re.IGNORECASE))
    )


def extract_url(text: str) -> str | None:
    matches = re.findall(r"https?://[^\s<>\"{}|\\^`\[\]]+", text, re.IGNORECASE)
    return matches[0] if matches else None


# ─── Barra de progreso ─────────────────────────────────────────────────────────

DIV = "▬" * 18


class ProgressState:
    def __init__(self):
        self.current = 0
        self.total = 0
        self.start_time = time.time()
        self.last_edit = 0.0

    def update(self, current: int, total: int):
        self.current = current
        self.total = total

    def render(self, label: str, emoji: str = "⬇️") -> str:
        elapsed = max(time.time() - self.start_time, 0.001)
        speed = self.current / elapsed if elapsed > 0 else 0
        if self.total > 0:
            pct = min(100.0, self.current / self.total * 100)
            remaining = (self.total - self.current) / speed if speed > 0 else -1
            bar = progress_bar(pct)
            return (
                f"{emoji}  <b>{bi(label)}</b>\n"
                f"<code>{DIV}</code>\n"
                f"<code>{bar}</code>  <b>{bi(f'{pct:.1f}%')}</b>\n\n"
                f"📦  {bi(fmt_size(self.current))} / {bi(fmt_size(self.total))}\n"
                f"⚡  {bi(fmt_size(int(speed)) + '/s')}  ·  ⏱  {bi(fmt_eta(remaining))}"
            )
        else:
            return (
                f"{emoji}  <b>{bi(label)}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"📦  {bi(fmt_size(self.current))} transferidos\n"
                f"⚡  {bi(fmt_size(int(speed)) + '/s')}"
            )


async def safe_edit(app: Client, chat_id: int, msg_id: int, text: str, markup=None):
    try:
        await app.edit_message_text(chat_id, msg_id, text, parse_mode=PM, reply_markup=markup)
    except Exception as e:
        logger.debug(f"safe_edit: {e}")


def cancel_kb(uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("⏹ Cancelar tarea", callback_data=f"cancel_{uid}")]])


# ─── Descarga MTProto (Pyrogram, hasta 2 GB) ───────────────────────────────────

async def download_telegram_file_mtproto(
    app: Client,
    message: Message,
    dest_path: Path,
    chat_id: int,
    status_msg_id: int,
    cancel_event: asyncio.Event,
) -> bool:
    progress = ProgressState()

    async def progress_cb(current: int, total: int):
        progress.update(current, total)
        now = time.time()
        if now - progress.last_edit >= 3.0:
            progress.last_edit = now
            await safe_edit(
                app, chat_id, status_msg_id,
                progress.render("Descargando archivo", "⬇️"),
                markup=cancel_kb(chat_id),
            )

    try:
        download_task  = asyncio.create_task(
            message.download(str(dest_path), progress=progress_cb)
        )
        cancel_waiter = asyncio.create_task(cancel_event.wait())
        done, pending = await asyncio.wait(
            {download_task, cancel_waiter},
            return_when=asyncio.FIRST_COMPLETED,
        )
        for t in pending:
            t.cancel()
            try:
                await t
            except (asyncio.CancelledError, Exception):
                pass
        if cancel_event.is_set():
            return False
        await download_task
        return dest_path.exists()
    except asyncio.CancelledError:
        return False
    except Exception as e:
        logger.error(f"Error descargando MTProto: {e}")
        return False


# ─── Descarga yt-dlp (YouTube · Instagram · TikTok · Twitter/X) ───────────────

QUALITY_MAP: dict[str, list] = {
    "best":  [],
    "1080":  ["-f", "bestvideo[height<=1080]+bestaudio/best[height<=1080]"],
    "720":   ["-f", "bestvideo[height<=720]+bestaudio/best[height<=720]"],
    "480":   ["-f", "bestvideo[height<=480]+bestaudio/best[height<=480]"],
    "360":   ["-f", "bestvideo[height<=360]+bestaudio/best[height<=360]"],
    "audio": ["-f", "bestaudio", "-x", "--audio-format", "mp3"],
}

QUALITY_LABELS = {
    "best":  "⭐ Mejor calidad",
    "1080":  "📺 1080p",
    "720":   "📺 720p",
    "480":   "📺 480p",
    "360":   "📺 360p",
    "audio": "🎵 Solo audio",
}


async def _kill_proc_on_cancel(cancel_event: asyncio.Event, proc) -> None:
    """Watcher: mata el proceso en cuanto se activa el evento de cancelación."""
    await cancel_event.wait()
    try:
        proc.kill()
    except Exception:
        pass


async def _run_ytdlp_proc(
    cmd: list,
    cancel_event: asyncio.Event,
) -> tuple[int, str]:
    """Ejecuta yt-dlp de forma async con cancelación instantánea."""
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        watcher = asyncio.create_task(_kill_proc_on_cancel(cancel_event, proc))
        try:
            await proc.wait()
        finally:
            watcher.cancel()
            try:
                await watcher
            except asyncio.CancelledError:
                pass

        if cancel_event.is_set():
            return -999, "cancelado"

        stderr_out = b""
        if proc.stderr:
            stderr_out = await proc.stderr.read()
        return proc.returncode, stderr_out.decode(errors="ignore")
    except asyncio.CancelledError:
        return -999, "cancelado"
    except Exception as e:
        return -1, str(e)


async def download_platform(
    url: str,
    dest_dir: Path,
    quality: str,
    chat_id: int,
    status_msg_id: int,
    app: Client,
    cancel_event: asyncio.Event,
    playlist: bool = False,
) -> tuple[list[Path], str]:
    quality_flags = QUALITY_MAP.get(quality, [])
    playlist_flag = [] if playlist else ["--no-playlist"]
    short_url = url[:55] + "…" if len(url) > 55 else url

    await safe_edit(
        app, chat_id, status_msg_id,
        f"🌐  <b>{bi('Analizando enlace...')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"🔗  <code>{esc(short_url)}</code>\n\n"
        f"⏳  {bi('Obteniendo información...')}",
        markup=cancel_kb(chat_id),
    )

    # ── Opciones base siempre presentes ──────────────────────────────────────
    BASE_OPTS = [
        "--no-check-certificate",
        "--geo-bypass",
        "--force-ipv4",
        "--no-warnings",
        "--retries", "10",
        "--fragment-retries", "15",
        "--retry-sleep", "linear=1::3",
        "--concurrent-fragments", "4",
        "--merge-output-format", "mp4",
        "--age-limit", "99",
        "-o", str(dest_dir / "%(title)s.%(ext)s"),
    ]

    # Formato adaptado a la calidad pedida, con múltiples fallbacks
    if quality == "audio":
        fmt_flags = ["-f", "bestaudio", "-x", "--audio-format", "mp3"]
    elif quality == "best":
        fmt_flags = [
            "-f",
            "bestvideo[ext=mp4]+bestaudio[ext=m4a]/"
            "bestvideo+bestaudio/best[ext=mp4]/best",
        ]
    else:
        h = quality  # "1080", "720", "480"
        fmt_flags = [
            "-f",
            f"bestvideo[height<={h}][ext=mp4]+bestaudio[ext=m4a]/"
            f"bestvideo[height<={h}]+bestaudio/"
            f"best[height<={h}][ext=mp4]/"
            f"best[height<={h}]/best",
        ]

    # ── Estrategias de descarga en orden de efectividad ────────────────────
    STRATEGIES = [
        {
            "label": "tv_embedded + ios",
            "extra": [
                "--extractor-args",
                "youtube:player_client=tv_embedded,ios",
            ],
        },
        {
            "label": "ios + android",
            "extra": [
                "--extractor-args",
                "youtube:player_client=ios,android,android_embedded",
            ],
        },
        {
            "label": "web_embedded + mweb",
            "extra": [
                "--extractor-args",
                "youtube:player_client=web_embedded,mweb,web",
                "--add-headers", "Referer:https://www.youtube.com/",
                "--user-agent",
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/124.0.0.0 Safari/537.36",
            ],
        },
        {
            "label": "formato simple",
            "extra": [
                "--extractor-args",
                "youtube:player_client=tv_embedded,ios,web",
                "--format", "best[ext=mp4]/best",
            ],
            "override_fmt": True,
        },
        {
            "label": "modo compatibilidad máxima",
            "extra": [
                "--extractor-args",
                "youtube:player_client=ios,tv_embedded,web,mweb,android",
                "--legacy-server-connect",
                "--format", "worst[ext=mp4]/worst",
                "--ignore-errors",
            ],
            "override_fmt": True,
        },
    ]

    # ── Obtener título ────────────────────────────────────────────────────
    title = "video"
    for client in ["tv_embedded,ios", "ios,android", "web"]:
        if cancel_event.is_set():
            return [], title
        try:
            info_r = await asyncio.get_running_loop().run_in_executor(
                None,
                lambda c=client: subprocess.run(
                    [
                        "yt-dlp", "--get-title", "--no-warnings",
                        "--no-check-certificate", "--geo-bypass",
                        "--extractor-args", f"youtube:player_client={c}",
                    ] + playlist_flag + [url],
                    capture_output=True, text=True, timeout=30,
                ),
            )
            if info_r.returncode == 0 and info_r.stdout.strip():
                title = info_r.stdout.strip().split("\n")[0]
                break
        except Exception:
            pass

    if cancel_event.is_set():
        return [], title

    qlabel = QUALITY_LABELS.get(quality, quality)

    # ── Bucle de intentos ────────────────────────────────────────────────
    for attempt_num, strategy in enumerate(STRATEGIES, 1):
        if cancel_event.is_set():
            return [], title

        # Limpiar archivos parciales entre intentos
        for f in dest_dir.glob("*.part"):
            try:
                f.unlink()
            except Exception:
                pass

        extra   = strategy["extra"]
        label   = strategy["label"]
        use_fmt = [] if strategy.get("override_fmt") else fmt_flags

        await safe_edit(
            app, chat_id, status_msg_id,
            f"⬇️  <b>{bi('Descargando...')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"🎞  <b>{esc(title[:55])}</b>\n"
            f"🔗  <code>{esc(short_url)}</code>\n"
            f"🎚  {bi(qlabel)}\n\n"
            f"🔄  {bi(f'Intento {attempt_num}/{len(STRATEGIES)}: {label}')}\n"
            f"⏳  {bi('Procesando...')}",
            markup=cancel_kb(chat_id),
        )

        cmd = ["yt-dlp"] + BASE_OPTS + extra + use_fmt + playlist_flag + [url]

        rc, stderr_txt = await _run_ytdlp_proc(cmd, cancel_event)

        if rc == -999:
            return [], title

        if rc == 0:
            files = [f for f in sorted(dest_dir.glob("*")) if f.suffix != ".part"]
            if files:
                logger.info(f"yt-dlp éxito en intento {attempt_num} ({label})")
                return files, title

        logger.warning(f"yt-dlp intento {attempt_num} ({label}) falló (rc={rc}): {stderr_txt[:200]}")

    # Todos los intentos fallaron
    logger.error(f"yt-dlp: todos los intentos fallaron para {url}")
    return [], title


# ─── Descarga directa de URL ───────────────────────────────────────────────────

async def download_url_direct(
    url: str,
    dest_dir: Path,
    chat_id: int,
    status_msg_id: int,
    app: Client,
    cancel_event: asyncio.Event,
) -> tuple[Path | None, str]:
    progress = ProgressState()
    headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}
    short_url = url[:55] + "…" if len(url) > 55 else url

    result_holder: list = [None]

    async def _do_stream_download():
        conn = aiohttp.TCPConnector(ssl=True)
        async with aiohttp.ClientSession(connector=conn, headers=headers) as session:
            async with session.head(url, allow_redirects=True, timeout=aiohttp.ClientTimeout(total=30)) as r:
                final_url = str(r.url)
            async with session.get(final_url, timeout=aiohttp.ClientTimeout(total=7200)) as resp:
                resp.raise_for_status()
                total = _safe_int(resp.headers.get("Content-Length", "0"))
                progress.total = total

                cd = resp.headers.get("Content-Disposition", "")
                file_name = None
                if "filename=" in cd:
                    m = re.search(r'filename[^;=\n]*=["\']?([^;\n"\']+)', cd)
                    if m:
                        file_name = unquote(m.group(1).strip())
                if not file_name:
                    path_part = unquote(urlparse(final_url).path)
                    file_name = Path(path_part).name or "archivo_descargado"
                if not Path(file_name).suffix:
                    ct = resp.headers.get("Content-Type", "")
                    ext = mimetypes.guess_extension(ct.split(";")[0].strip()) or ".bin"
                    file_name += ext
                file_name = sanitize_name(Path(file_name).stem) + Path(file_name).suffix
                file_path = dest_dir / file_name

                async with aiofiles.open(str(file_path), "wb") as f:
                    async for chunk in resp.content.iter_chunked(512 * 1024):
                        await f.write(chunk)
                        progress.update(progress.current + len(chunk), total)
                        now = time.time()
                        if now - progress.last_edit >= 3.0:
                            progress.last_edit = now
                            await safe_edit(
                                app, chat_id, status_msg_id,
                                progress.render("Descargando archivo", "⬇️"),
                                markup=cancel_kb(chat_id),
                            )
                result_holder.append((file_path, Path(file_name).stem))

    try:
        dl_task       = asyncio.create_task(_do_stream_download())
        cancel_waiter = asyncio.create_task(cancel_event.wait())
        done, pending = await asyncio.wait(
            {dl_task, cancel_waiter},
            return_when=asyncio.FIRST_COMPLETED,
        )
        for t in pending:
            t.cancel()
            try:
                await t
            except (asyncio.CancelledError, Exception):
                pass
        if cancel_event.is_set():
            return None, ""
        await dl_task
        if len(result_holder) > 1:
            return result_holder[1]

    except Exception as e:
        logger.error(f"Error descarga directa: {e}")

    # Fallback yt-dlp
    try:
        await safe_edit(
            app, chat_id, status_msg_id,
            f"🔄  <b>{bi('Método alternativo...')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"🔗  <code>{esc(short_url)}</code>\n\n"
            f"⏳  {bi('Reintentando descarga...')}",
            markup=cancel_kb(chat_id),
        )
        fallback_proc = await asyncio.create_subprocess_exec(
            "yt-dlp", "--no-playlist",
            "--extractor-args",
            "youtube:player_client=ios,web,mweb,android,android_embedded",
            "--no-check-certificate",
            "--force-ipv4",
            "--no-warnings",
            "-o", str(dest_dir / "%(title)s.%(ext)s"),
            url,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        watcher = asyncio.create_task(_kill_proc_on_cancel(cancel_event, fallback_proc))
        try:
            await fallback_proc.wait()
        finally:
            watcher.cancel()
            try:
                await watcher
            except asyncio.CancelledError:
                pass
        if cancel_event.is_set():
            return None, ""
        files = list(dest_dir.glob("*"))
        if files:
            return files[0], files[0].stem
    except Exception as e2:
        logger.error(f"yt-dlp fallback: {e2}")

    return None, "archivo"


# ─── Detección de binario 7z ───────────────────────────────────────────────────

def _find_7z_binary() -> str | None:
    for name in ("7z", "7za", "7zz", "7zzs"):
        if shutil.which(name):
            return name
    return None


# ─── Compresión py7zr (fallback sin binario) ───────────────────────────────────

async def _compress_py7zr(
    file_path: Path,
    archive_path: Path,
    archive_name: str,
    chat_id: int,
    status_msg_id: int,
    app: Client,
) -> Path:
    file_size = file_path.stat().st_size
    await safe_edit(
        app, chat_id, status_msg_id,
        f"🗜  <b>{bi('Comprimiendo...')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"📂  <b>{esc(archive_name[:55])}</b>\n"
        f"📦  {bi(fmt_size(file_size))}\n\n"
        f"<code>{progress_bar(0)}</code>  <b>{bi('0.0%')}</b>\n\n"
        f"🗜  {bi('Compresión py7zr · LZMA2 nivel 5')}",
    )

    done_event = asyncio.Event()
    # Estimación conservadora: el .7z final pesa ~60% del original para
    # contenido típico. Usamos eso como "100%" mientras crece el archivo.
    est_final = max(int(file_size * 0.60), 1)

    async def progress_monitor():
        """Sondea cada 2.5 s el tamaño del .7z parcial y actualiza la barra."""
        while not done_event.is_set():
            try:
                await asyncio.wait_for(done_event.wait(), timeout=2.5)
                break
            except asyncio.TimeoutError:
                pass
            try:
                cur_size = archive_path.stat().st_size if archive_path.exists() else 0
            except OSError:
                cur_size = 0
            pct = min(99.0, (cur_size / est_final) * 100)
            bar = progress_bar(pct)
            await safe_edit(
                app, chat_id, status_msg_id,
                f"🗜  <b>{bi('Comprimiendo...')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"📂  <b>{esc(archive_name[:55])}</b>\n"
                f"📦  {bi(fmt_size(file_size))}  →  {bi(fmt_size(cur_size))}\n\n"
                f"<code>{bar}</code>  <b>{bi(f'{pct:.1f}%')}</b>\n\n"
                f"🗜  {bi('Compresión py7zr · LZMA2 nivel 5')}",
            )

    def _do_compress():
        filters = [{"id": py7zr.FILTER_LZMA2, "preset": 5}]
        with py7zr.SevenZipFile(str(archive_path), mode="w", filters=filters) as zf:
            zf.write(str(file_path), file_path.name)

    monitor_task = asyncio.create_task(progress_monitor())
    try:
        await asyncio.get_running_loop().run_in_executor(None, _do_compress)
    finally:
        done_event.set()
        try:
            await monitor_task
        except Exception:
            pass

    if not archive_path.exists():
        raise RuntimeError("No se generó el archivo comprimido (py7zr).")

    await safe_edit(
        app, chat_id, status_msg_id,
        f"🗜  <b>{bi('Compresión completa')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"📂  <b>{esc(archive_name[:55])}</b>\n"
        f"📦  {bi(fmt_size(file_size))}  →  {bi(fmt_size(archive_path.stat().st_size))}\n\n"
        f"<code>{'█' * 18}</code>  <b>{bi('100.0%')}</b>\n\n"
        f"✅  {bi('Listo para subir a la nube...')}",
    )
    return archive_path


# ─── Compresión 7z con barra de progreso en tiempo real ───────────────────────

async def compress_file_with_progress(
    file_path: Path,
    output_dir: Path,
    archive_name: str,
    chat_id: int,
    status_msg_id: int,
    app: Client,
    cancel_event: asyncio.Event | None = None,
) -> Path:
    archive_path = output_dir / f"{archive_name}.7z"

    seven_z = _find_7z_binary()
    if not seven_z:
        if _PY7ZR_AVAILABLE:
            logger.info("Binario 7z no encontrado — usando py7zr como fallback")
            return await _compress_py7zr(file_path, archive_path, archive_name, chat_id, status_msg_id, app)
        raise RuntimeError(
            "7z no está instalado y py7zr no está disponible. "
            "Instala p7zip o py7zr en el servidor."
        )

    cmd = [
        seven_z, "a", "-t7z",
        "-mx=5",      # nivel normal: buen ratio tamaño/velocidad
        "-mfb=64",    # word size mayor → mejor ratio LZMA2
        "-ms=on",     # modo sólido → mejor compresión en sets de archivos
        "-mmt=on",    # multi-hilo → mantiene velocidad razonable
        "-bsp1",
        str(archive_path), str(file_path),
    ]

    file_size = file_path.stat().st_size
    current_pct: list[float] = [0.0]
    last_edit: list[float] = [0.0]

    proc = await asyncio.create_subprocess_exec(
        *cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
    )

    async def read_stdout():
        buf = b""
        while True:
            chunk = await proc.stdout.read(256)
            if not chunk:
                break
            buf += chunk
            matches = re.findall(rb"(\d{1,3})%", buf)
            if matches:
                current_pct[0] = float(matches[-1])
            if len(buf) > 4096:
                buf = buf[-512:]
            now = time.time()
            if now - last_edit[0] >= 2.5:
                last_edit[0] = now
                pct = current_pct[0]
                bar = progress_bar(pct)
                await safe_edit(
                    app, chat_id, status_msg_id,
                    f"🗜  <b>{bi('Comprimiendo...')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"📂  <b>{esc(archive_name[:55])}</b>\n"
                    f"📦  {bi(fmt_size(file_size))}\n\n"
                    f"<code>{bar}</code>  <b>{bi(f'{pct:.1f}%')}</b>\n\n"
                    f"🗜  {bi('Compresión 7z · nivel 5 · máxima reducción de tamaño')}",
                    markup=cancel_kb(chat_id),
                )

    progress_task = asyncio.create_task(read_stdout())
    watcher_task  = asyncio.create_task(
        _kill_proc_on_cancel(cancel_event, proc)
    ) if cancel_event else None

    try:
        await proc.wait()
    finally:
        if watcher_task:
            watcher_task.cancel()
            try:
                await watcher_task
            except asyncio.CancelledError:
                pass
        progress_task.cancel()
        try:
            await progress_task
        except asyncio.CancelledError:
            pass

    if cancel_event and cancel_event.is_set():
        raise asyncio.CancelledError("Cancelado por el usuario")

    if proc.returncode != 0:
        stderr_data = await proc.stderr.read()
        raise RuntimeError(f"Error al comprimir: {stderr_data.decode(errors='ignore')[:300]}")

    if not archive_path.exists():
        raise RuntimeError("No se generó el archivo comprimido.")

    await safe_edit(
        app, chat_id, status_msg_id,
        f"🗜  <b>{bi('Compresión completa')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"📂  <b>{esc(archive_name[:55])}</b>\n"
        f"📦  {bi(fmt_size(file_size))}\n\n"
        f"<code>{'█' * 18}</code>  <b>{bi('100.0%')}</b>\n\n"
        f"✅  {bi('Listo para subir a la nube...')}",
    )

    return archive_path


# ─── Subida a la nube (aiohttp streaming con progreso real) ────────────────────

_UPLOAD_CHUNK = 256 * 1024   # 256 KB por chunk


async def upload_to_cloud(
    archive_path: Path,
    title: str,
    chat_id: int,
    status_msg_id: int,
    app: Client,
    cancel_event: asyncio.Event | None = None,
) -> tuple[str, str]:
    identifier = re.sub(
        r"[^a-zA-Z0-9_-]", "-",
        f"tgbot-{sanitize_name(title)}-{uuid.uuid4().hex[:8]}"
    )[:80]

    total_size   = archive_path.stat().st_size
    uploaded_ref = [0]
    start_time   = time.time()

    await safe_edit(
        app, chat_id, status_msg_id,
        f"☁️  <b>{bi('Subiendo a la nube...')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"📂  <b>{esc(title[:50])}</b>\n"
        f"📦  {bi(fmt_size(total_size))}\n\n"
        f"<code>{'░' * 18}</code>  <b>{bi('0.0%')}</b>\n\n"
        f"⏳  {bi('Iniciando transferencia...')}",
        markup=cancel_kb(chat_id),
    )

    # ── Generador async que lee el archivo por chunks y actualiza el progreso ──
    async def file_sender():
        async with aiofiles.open(str(archive_path), "rb") as f:
            while True:
                if cancel_event and cancel_event.is_set():
                    return
                chunk = await f.read(_UPLOAD_CHUNK)
                if not chunk:
                    break
                uploaded_ref[0] += len(chunk)
                yield chunk

    # ── Tarea que actualiza el mensaje de progreso cada 3 s ──────────────────
    async def progress_updater():
        while True:
            await asyncio.sleep(3)
            ub      = uploaded_ref[0]
            elapsed = max(time.time() - start_time, 0.001)
            speed   = ub / elapsed if elapsed > 0 else 0
            pct     = min(99.0, ub / total_size * 100) if total_size > 0 else 0
            rem     = (total_size - ub) / speed if speed > 0 else -1
            bar     = progress_bar(pct)
            await safe_edit(
                app, chat_id, status_msg_id,
                f"☁️  <b>{bi('Subiendo a la nube...')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"📂  <b>{esc(title[:50])}</b>\n"
                f"📦  {bi(fmt_size(total_size))}\n\n"
                f"<code>{bar}</code>  <b>{bi(f'{pct:.1f}%')}</b>\n\n"
                f"📤  {bi(fmt_size(ub))} / {bi(fmt_size(total_size))}\n"
                f"⚡  {bi(fmt_size(int(speed)) + '/s')}  ·  ⏱  {bi(fmt_eta(rem))}",
                markup=cancel_kb(chat_id),
            )

    # ── Headers S3 de Archive.org ─────────────────────────────────────────────
    headers = {
        "authorization":             f"LOW {ARCHIVE_ACCESS}:{ARCHIVE_SECRET}",
        "x-archive-auto-make-bucket": "1",
        "x-archive-queue-derive":     "0",
        "x-archive-meta-mediatype":   "data",
        "x-archive-meta-title":       title,
        "x-archive-meta-description": f"Subido por Telegram Bot. Nombre: {title}",
        "x-archive-meta-subject":     "telegram-bot-upload",
        "content-type":               "application/octet-stream",
        "content-length":             str(total_size),
    }
    upload_url = (
        f"https://s3.us.archive.org/{identifier}/"
        f"{archive_path.name}"
    )

    async def _do_upload():
        connector = aiohttp.TCPConnector(ssl=False, limit=1)
        timeout   = aiohttp.ClientTimeout(total=7200, connect=30)
        async with aiohttp.ClientSession(connector=connector) as session:
            async with session.put(
                upload_url,
                headers=headers,
                data=file_sender(),
                timeout=timeout,
            ) as resp:
                if resp.status not in (200, 201):
                    body = await resp.text()
                    raise RuntimeError(
                        f"Archive.org S3 error {resp.status}: {body[:200]}"
                    )

    upload_task   = asyncio.create_task(_do_upload())
    updater_task  = asyncio.create_task(progress_updater())
    cancel_waiter = asyncio.create_task(cancel_event.wait()) if cancel_event else None

    try:
        tasks_to_watch = {upload_task}
        if cancel_waiter:
            tasks_to_watch.add(cancel_waiter)
        done, pending = await asyncio.wait(
            tasks_to_watch,
            return_when=asyncio.FIRST_COMPLETED,
        )
        for t in pending:
            t.cancel()
            try:
                await t
            except (asyncio.CancelledError, Exception):
                pass
        if cancel_event and cancel_event.is_set():
            raise asyncio.CancelledError("Cancelado por el usuario")
        await upload_task
    finally:
        updater_task.cancel()
        try:
            await updater_task
        except asyncio.CancelledError:
            pass

    link = f"https://archive.org/download/{identifier}/{archive_path.name}"
    return link, identifier


# ─── Subida al Servidor de Almacenamiento Local ───────────────────────────────
#
# Copia el archivo al directorio del servidor con un identificador
# unguessable (96 bits). Genera un enlace permanente firmado vía HMAC.
# Las descargas posteriores no consumen ancho de banda hacia archive.org;
# si el servidor está detrás de un proxy nacional cubano, no descuenta MB.
#

def _sign_path(path: str) -> str:
    """Firma HMAC-SHA256 truncada (16 bytes hex) para verificar el enlace."""
    return hmac.new(STORAGE_TOKEN_SECRET, path.encode(), hashlib.sha256).hexdigest()[:32]


def _make_storage_link(identifier: str, filename: str, base: str | None = None) -> str:
    """Construye la URL firmada de descarga.

    Si se pasa `base`, se usa esa URL en lugar de STORAGE_PUBLIC_URL.
    Útil para generar enlaces a mirrors (p.ej. proxy cubano)."""
    rel = f"{identifier}/{filename}"
    sig = _sign_path(rel)
    base = (base or STORAGE_PUBLIC_URL).rstrip("/")
    return f"{base}/d/{sig}/{quote(identifier)}/{quote(filename)}"


def _make_storage_links(identifier: str, filename: str) -> list[str]:
    """Devuelve [URL_principal, *URLs_mirrors] sin duplicados."""
    urls = [_make_storage_link(identifier, filename)]
    seen = {STORAGE_PUBLIC_URL.rstrip("/")}
    for m in STORAGE_MIRRORS:
        if m and m.rstrip("/") not in seen:
            seen.add(m.rstrip("/"))
            urls.append(_make_storage_link(identifier, filename, base=m))
    return urls


def _make_manifest_link(identifier: str, filename: str, base: str | None = None) -> str:
    """URL del manifest (sha256 + tamaño + mirrors). Cacheable para siempre."""
    rel = f"{identifier}/{filename}"
    sig = _sign_path(rel)
    base = (base or STORAGE_PUBLIC_URL).rstrip("/")
    return f"{base}/m/{sig}/{quote(identifier)}/{quote(filename)}"


async def _enforce_storage_quota():
    """Borra los archivos más antiguos si se excede la capacidad o el TTL."""
    try:
        # 1) TTL por archivo
        if STORAGE_FILE_TTL_DAYS > 0:
            cutoff = datetime.now() - timedelta(days=STORAGE_FILE_TTL_DAYS)
            cutoff_str = cutoff.strftime("%Y-%m-%d %H:%M:%S")
            async with aiosqlite.connect(DB_FILE) as db:
                async with db.execute(
                    "SELECT identifier FROM storage_files WHERE created_at < ?",
                    (cutoff_str,),
                ) as cur:
                    expired = [row[0] for row in await cur.fetchall()]
            for ident in expired:
                await delete_storage_file(ident)
                logger.info(f"Storage: archivo expirado eliminado ({ident})")

        # 2) Capacidad máxima total
        max_bytes = STORAGE_MAX_GB * 1024 ** 3
        if max_bytes <= 0:
            return
        async with aiosqlite.connect(DB_FILE) as db:
            async with db.execute(
                "SELECT identifier, size FROM storage_files "
                "ORDER BY created_at ASC"
            ) as cur:
                rows = await cur.fetchall()
        total = sum(r[1] for r in rows)
        if total <= max_bytes:
            return
        # Eliminar los más viejos hasta liberar espacio (deja un 10% de margen)
        target = int(max_bytes * 0.9)
        for ident, size in rows:
            if total <= target:
                break
            await delete_storage_file(ident)
            total -= size
            logger.info(f"Storage: purgado por cuota ({ident}, libera {fmt_size(size)})")
    except Exception as e:
        logger.error(f"Storage: error aplicando cuota: {e}")


async def upload_to_local_storage(
    archive_path: Path,
    title: str,
    chat_id: int,
    status_msg_id: int,
    app: Client,
    user_id: int,
    cancel_event: asyncio.Event | None = None,
) -> tuple[str, str]:
    # Identificador unguessable (96 bits) — evita enumeración del catálogo
    identifier = f"{sanitize_name(title)[:40]}-{_secrets.token_urlsafe(12)}"
    identifier = re.sub(r"[^a-zA-Z0-9_\-]", "", identifier)[:80] or _secrets.token_urlsafe(12)

    dest_dir   = STORAGE_DIR / identifier
    dest_dir.mkdir(parents=True, exist_ok=True)
    dest_path  = dest_dir / archive_path.name

    total_size = archive_path.stat().st_size
    copied_ref = [0]
    start_time = time.time()

    await safe_edit(
        app, chat_id, status_msg_id,
        f"💾  <b>{bi('Guardando en el servidor...')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"📂  <b>{esc(title[:50])}</b>\n"
        f"📦  {bi(fmt_size(total_size))}\n\n"
        f"<code>{'░' * 18}</code>  <b>{bi('0.0%')}</b>\n\n"
        f"⏳  {bi('Iniciando transferencia local...')}",
        markup=cancel_kb(chat_id),
    )

    async def progress_updater():
        while True:
            await asyncio.sleep(2)
            cb      = copied_ref[0]
            elapsed = max(time.time() - start_time, 0.001)
            speed   = cb / elapsed if elapsed > 0 else 0
            pct     = min(99.0, cb / total_size * 100) if total_size > 0 else 0
            rem     = (total_size - cb) / speed if speed > 0 else -1
            bar     = progress_bar(pct)
            await safe_edit(
                app, chat_id, status_msg_id,
                f"💾  <b>{bi('Guardando en el servidor...')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"📂  <b>{esc(title[:50])}</b>\n"
                f"📦  {bi(fmt_size(total_size))}\n\n"
                f"<code>{bar}</code>  <b>{bi(f'{pct:.1f}%')}</b>\n\n"
                f"📤  {bi(fmt_size(cb))} / {bi(fmt_size(total_size))}\n"
                f"⚡  {bi(fmt_size(int(speed)) + '/s')}  ·  ⏱  {bi(fmt_eta(rem))}",
                markup=cancel_kb(chat_id),
            )

    async def _do_copy():
        async with aiofiles.open(str(archive_path), "rb") as src, \
                   aiofiles.open(str(dest_path), "wb") as dst:
            while True:
                if cancel_event and cancel_event.is_set():
                    return
                chunk = await src.read(_UPLOAD_CHUNK)
                if not chunk:
                    break
                await dst.write(chunk)
                copied_ref[0] += len(chunk)

    copy_task    = asyncio.create_task(_do_copy())
    updater_task = asyncio.create_task(progress_updater())
    cancel_waiter = asyncio.create_task(cancel_event.wait()) if cancel_event else None

    try:
        watch = {copy_task}
        if cancel_waiter:
            watch.add(cancel_waiter)
        done, pending = await asyncio.wait(watch, return_when=asyncio.FIRST_COMPLETED)
        for t in pending:
            t.cancel()
            try:
                await t
            except (asyncio.CancelledError, Exception):
                pass
        if cancel_event and cancel_event.is_set():
            shutil.rmtree(dest_dir, ignore_errors=True)
            raise asyncio.CancelledError("Cancelado por el usuario")
        await copy_task
    finally:
        updater_task.cancel()
        try:
            await updater_task
        except asyncio.CancelledError:
            pass

    # Registrar en la base de datos y aplicar cuotas
    await register_storage_file(identifier, archive_path.name, total_size, user_id)
    asyncio.create_task(_enforce_storage_quota())
    # Calcular sha256 en segundo plano (para Digest, manifest e integridad)
    asyncio.create_task(compute_storage_sha256(identifier, dest_path))

    link = _make_storage_link(identifier, archive_path.name)
    return link, identifier


# ─── Resultado como archivo .txt (solo el enlace) ─────────────────────────────

async def send_result_txt(
    app: Client,
    chat_id: int,
    title: str,
    link: str,
    identifier: str,
    archive_size: int,
):
    safe_title = sanitize_name(title)
    txt_name = f"{safe_title}.txt"
    txt_path = TEMP_DIR / txt_name

    async with aiofiles.open(str(txt_path), "w", encoding="utf-8") as f:
        await f.write(link + "\n")

    caption = (
        f"╔══════════════════════════╗\n"
        f"║  ✅  <b>{bi('¡Listo en la Nube!')}</b>  ║\n"
        f"╚══════════════════════════╝\n\n"
        f"🎯  <b>{esc(title[:60])}</b>\n"
        f"📦  {bi(fmt_size(archive_size))}  ·  🗜  7z  ·  {bi('Archivo único')}\n\n"
        f"📄  {bi('El enlace de descarga está en el archivo adjunto')} 👆\n\n"
        f"⏰  <i>Disponible en la nube en unos minutos.</i>"
    )

    await app.send_document(
        chat_id,
        str(txt_path),
        caption=caption,
        parse_mode=PM,
        file_name=txt_name,
    )
    try:
        txt_path.unlink()
    except Exception:
        pass


# ─── Verificar cuota ───────────────────────────────────────────────────────────

async def check_quota(app: Client, uid: int, uname: str | None, chat_id: int) -> bool:
    if is_admin(uid, uname):
        return True
    usage = await get_daily_usage(uid)
    quota = await get_quota(uid)
    if usage >= quota:
        await app.send_message(
            chat_id,
            f"⚠️  <b>{bi('Cuota Diaria Agotada')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"Has utilizado  <b>{usage}/{quota}</b>  subidas hoy.\n"
            f"Tu cuota se renueva automáticamente a medianoche.\n\n"
            f"<i>¿Necesitas más? Contacta al administrador.</i>",
            parse_mode=PM,
            reply_markup=admin_contact_btn(),
        )
        return False
    return True


# ─── Verificar acceso ─────────────────────────────────────────────────────────

async def check_access(app: Client, message: Message) -> bool:
    if not message.from_user:
        return False
    uid   = message.from_user.id
    uname = message.from_user.username
    fname = message.from_user.first_name or "Usuario"

    if is_banned(uid, uname):
        await message.reply_text(
            f"🚫  <b>{bi('Cuenta Bloqueada')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"Tu cuenta ha sido bloqueada por el administrador.\n"
            f"Si crees que es un error, contáctalo directamente.",
            parse_mode=PM,
            reply_markup=admin_contact_btn(uid),
        )
        return False

    if not is_allowed(uid, uname):
        if _ADMIN_ID:
            try:
                await app.send_message(
                    _ADMIN_ID,
                    f"🔔  <b>{bi('Solicitud de Acceso')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"👤  <b>{esc(fname)}</b>\n"
                    f"🆔  <code>{uid}</code>\n"
                    f"📧  @{esc(uname or 'sin_usuario')}",
                    parse_mode=PM,
                    reply_markup=InlineKeyboardMarkup([[
                        InlineKeyboardButton("✅ Aprobar", callback_data=f"approve_{uid}"),
                        InlineKeyboardButton("❌ Rechazar", callback_data=f"reject_{uid}"),
                    ]]),
                )
            except Exception:
                pass

        await message.reply_text(
            f"🔐  <b>{bi('Acceso Restringido')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"No tienes permiso para usar este bot.\n\n"
            f"Tu solicitud fue enviada al administrador.\n"
            f"Te notificaremos cuando sea aprobada. ✉️",
            parse_mode=PM,
            reply_markup=admin_contact_btn(uid),
        )
        return False

    return True


# ─── Procesador de trabajos ────────────────────────────────────────────────────

async def process_job(app: Client, job: dict):
    uid        = job["user_id"]
    chat_id    = job["chat_id"]
    uname      = job.get("username") or ""
    first_name = job.get("first_name") or ""
    job_type   = job["type"]
    cancel_ev  = job["cancel_event"]

    work_dir = TEMP_DIR / f"job_{uid}_{int(time.time() * 1000)}"
    work_dir.mkdir(parents=True, exist_ok=True)
    status_msg = None

    try:
        status_msg = await app.send_message(
            chat_id,
            f"🚀  <b>{bi('Procesando tu solicitud...')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"⏳  {bi('Preparando descarga...')}",
            parse_mode=PM,
            reply_markup=cancel_kb(uid),
        )
        smid = status_msg.id

        active_tasks[uid] = {
            "status": "Procesando",
            "cancel_event": cancel_ev,
            "progress_msg_id": smid,
            "chat_id": chat_id,
        }

        if cancel_ev.is_set():
            await safe_edit(app, chat_id, smid,
                f"⏹  <b>{bi('Tarea cancelada por el usuario.')}</b>")
            return

        # ── Descarga ───────────────────────────────────────────────────────────
        downloaded_files: list[Path] = []
        title = "archivo"

        if job_type == "file":
            original_msg: Message = job["message"]
            doc = (
                original_msg.document or original_msg.video or original_msg.audio
                or original_msg.voice or original_msg.video_note
                or original_msg.animation or original_msg.photo
            )
            fname = getattr(doc, "file_name", None) or "archivo"
            stem   = Path(fname).stem
            raw_suffix = Path(fname).suffix
            if not raw_suffix:
                if original_msg.photo:
                    raw_suffix = ".jpg"
                elif original_msg.voice:
                    raw_suffix = ".ogg"
                elif original_msg.video or original_msg.video_note:
                    raw_suffix = ".mp4"
                elif original_msg.audio:
                    raw_suffix = ".mp3"
                else:
                    raw_suffix = ".bin"
            suffix = raw_suffix
            dest   = work_dir / (sanitize_name(stem) + suffix)
            title  = stem

            ok = await download_telegram_file_mtproto(
                app, original_msg, dest, chat_id, smid, cancel_ev
            )
            if ok and dest.exists():
                downloaded_files = [dest]

        elif job_type == "platform":
            url      = job["url"]
            quality  = job.get("quality", "best")
            playlist = job.get("playlist", False)
            files, title = await download_platform(
                url, work_dir, quality, chat_id, smid, app, cancel_ev, playlist
            )
            downloaded_files = files

        elif job_type == "url":
            url = job["url"]
            f, title = await download_url_direct(url, work_dir, chat_id, smid, app, cancel_ev)
            if f:
                downloaded_files = [f]

        if cancel_ev.is_set():
            await safe_edit(app, chat_id, smid,
                f"⏹  <b>{bi('Tarea cancelada por el usuario.')}</b>")
            return

        if not downloaded_files:
            await safe_edit(
                app, chat_id, smid,
                f"❌  <b>{bi('Error al descargar')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"No se pudo obtener el archivo.\n"
                f"Verifica el enlace e intenta de nuevo.",
            )
            return

        # ── Comprimir y subir ──────────────────────────────────────────────────
        for file_path in downloaded_files:
            if cancel_ev.is_set():
                break

            file_title   = file_path.stem if len(downloaded_files) > 1 else title
            archive_name = sanitize_name(file_title)

            try:
                archive_path = await compress_file_with_progress(
                    file_path, work_dir, archive_name, chat_id, smid, app, cancel_ev
                )
            except asyncio.CancelledError:
                break
            except Exception as e:
                await safe_edit(app, chat_id, smid,
                    f"❌  <b>{bi('Error al comprimir')}</b>\n\n"
                    f"<code>{esc(str(e)[:200])}</code>")
                continue

            if cancel_ev.is_set():
                break

            dest = await get_upload_dest()
            try:
                if dest == "local":
                    link, identifier = await upload_to_local_storage(
                        archive_path, file_title, chat_id, smid, app, uid, cancel_ev
                    )
                else:
                    link, identifier = await upload_to_cloud(
                        archive_path, file_title, chat_id, smid, app, cancel_ev
                    )
            except asyncio.CancelledError:
                break
            except Exception as e:
                dest_label = "el servidor local" if dest == "local" else "la nube"
                await safe_edit(app, chat_id, smid,
                    f"❌  <b>{bi(f'Error al subir a {dest_label}')}</b>\n\n"
                    f"<code>{esc(str(e)[:200])}</code>")
                continue

            archive_size = archive_path.stat().st_size
            await add_history(uid, uname, first_name, file_title, link, archive_size)
            await increment_usage(uid)

            try:
                await app.delete_messages(chat_id, smid)
            except Exception:
                pass

            await send_result_txt(app, chat_id, file_title, link, identifier, archive_size)

            if _ADMIN_ID and uid != _ADMIN_ID:
                try:
                    await app.send_message(
                        _ADMIN_ID,
                        f"📤  <b>{bi('Nueva subida completada')}</b>\n"
                        f"<code>{DIV}</code>\n\n"
                        f"👤  <b>{esc(first_name)}</b>  (@{esc(uname or '—')})\n"
                        f"🆔  <code>{uid}</code>\n"
                        f"📂  <b>{esc(file_title[:50])}</b>\n"
                        f"📦  {bi(fmt_size(archive_size))}\n\n"
                        f'🔗  <a href="{link}">Descargar archivo</a>',
                        parse_mode=PM,
                        disable_web_page_preview=True,
                    )
                except Exception:
                    pass

    except Exception as e:
        logger.error(f"Error en process_job: {e}", exc_info=True)
        if status_msg:
            try:
                await safe_edit(app, chat_id, status_msg.id,
                    f"❌  <b>{bi('Error inesperado')}</b>\n\n"
                    f"<code>{esc(str(e)[:200])}</code>")
            except Exception:
                pass
    finally:
        active_tasks.pop(uid, None)
        shutil.rmtree(work_dir, ignore_errors=True)


def _cleanup_pending(d: dict, max_entries: int = 200):
    if len(d) > max_entries:
        keys_to_del = list(d.keys())[: len(d) - max_entries]
        for k in keys_to_del:
            d.pop(k, None)


async def enqueue_job(app: Client, uid: int, job: dict) -> int:
    if uid not in job_queues:
        job_queues[uid] = asyncio.Queue()
        asyncio.create_task(queue_worker(app, uid))
    pos = job_queues[uid].qsize()
    job["cancel_event"] = asyncio.Event()
    await job_queues[uid].put(job)
    _cleanup_pending(pending_quality)
    _cleanup_pending(pending_playlist)
    return pos


async def queue_worker(app: Client, uid: int):
    while True:
        job = await job_queues[uid].get()
        try:
            await process_job(app, job)
        except Exception as e:
            logger.error(f"queue_worker uid={uid}: {e}", exc_info=True)
        finally:
            job_queues[uid].task_done()


# ─── Comandos ─────────────────────────────────────────────────────────────────

async def cmd_start(app: Client, message: Message):
    uid   = message.from_user.id
    uname = message.from_user.username
    fname = esc(message.from_user.first_name or "Usuario")

    if is_banned(uid, uname):
        await message.reply_text(
            f"🚫  <b>{bi('Cuenta Bloqueada')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"Tu cuenta ha sido bloqueada. Contacta al administrador.",
            parse_mode=PM,
            reply_markup=admin_contact_btn(uid),
        )
        return

    if not is_allowed(uid, uname):
        await message.reply_text(
            f"🔐  <b>{bi('Acceso Restringido')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"No tienes permiso para usar este bot.\n"
            f"Contacta al administrador para solicitar acceso.",
            parse_mode=PM,
            reply_markup=admin_contact_btn(uid),
        )
        return

    admin_badge = "  👑" if is_admin(uid, uname) else ""
    usage = await get_daily_usage(uid)
    quota = await get_quota(uid)
    quota_str = "∞" if is_admin(uid, uname) else str(quota)

    await message.reply_text(
        f"🤖  <b>{bi('Bot Archivador')}  ·  v3.1</b>{admin_badge}\n"
        f"<code>{DIV}</code>\n\n"
        f"👋  <b>{bi(f'Bienvenido, {fname}!')}</b>\n\n"
        f"📌  Envíame cualquiera de estos:\n\n"
        f"  📁  Archivo de Telegram  <i>(hasta 2 GB)</i>\n"
        f"  🎬  YouTube · Playlist completa\n"
        f"  📸  Instagram · TikTok · Twitter/X\n"
        f"  🌐  Cualquier enlace de descarga\n\n"
        f"📊  <b>Uso hoy:</b>  {bi(str(usage))}/{bi(quota_str)}\n\n"
        f"<i>Escribe /help para ver los comandos disponibles.</i>",
        parse_mode=PM,
    )


async def cmd_help(app: Client, message: Message):
    if not await check_access(app, message):
        return
    uid   = message.from_user.id
    uname = message.from_user.username

    admin_section = ""
    if is_admin(uid, uname):
        admin_section = (
            f"\n\n👑  <b>{bi('Comandos de Administrador')}</b>\n"
            f"<code>{DIV}</code>\n"
            f"  /add_user        —  Agregar usuario por ID o @usuario\n"
            f"  /ban_user        —  Banear usuario\n"
            f"  /list_user       —  Ver todos los usuarios\n"
            f"  /set_cuota       —  Cambiar cuota diaria de un usuario\n"
            f"  /cambiar_subida  —  Cambiar destino: archive.org / servidor local\n"
            f"  /storage         —  Estado del servidor de almacenamiento"
        )

    await message.reply_text(
        f"📋  <b>{bi('Comandos Disponibles')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"  /start      —  Inicio y bienvenida\n"
        f"  /help       —  Este mensaje de ayuda\n"
        f"  /status     —  Estado de tu tarea actual\n"
        f"  /cancelar   —  Cancelar tarea en curso\n"
        f"  /historial  —  Tus últimas 10 subidas"
        + admin_section,
        parse_mode=PM,
    )


async def cmd_status(app: Client, message: Message):
    if not await check_access(app, message):
        return
    uid = message.from_user.id
    task = active_tasks.get(uid)
    queue_size = job_queues[uid].qsize() if uid in job_queues else 0

    if not task and queue_size == 0:
        await message.reply_text(
            f"✅  <b>{bi('Sin tareas activas')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"No tienes ninguna tarea en proceso.\n"
            f"Envíame un archivo o enlace para comenzar.",
            parse_mode=PM,
        )
    elif task:
        cola_txt = f"\n📋  {bi(str(queue_size))} más en cola" if queue_size > 0 else ""
        await message.reply_text(
            f"⚙️  <b>{bi('Tarea en proceso')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"🔄  {bi(task.get('status', 'Procesando'))}"
            + cola_txt
            + f"\n\n<i>Usa /cancelar para detenerla.</i>",
            parse_mode=PM,
        )
    else:
        await message.reply_text(
            f"⏳  <b>{bi('Cola de espera')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"📋  {bi(str(queue_size))} tarea(s) en cola.",
            parse_mode=PM,
        )


async def cmd_cancelar(app: Client, message: Message):
    if not await check_access(app, message):
        return
    uid = message.from_user.id
    task = active_tasks.get(uid)
    if task:
        task["cancel_event"].set()
        await message.reply_text(
            f"⏹  <b>{bi('Cancelando...')}</b>\n\n"
            f"La tarea en curso será detenida.",
            parse_mode=PM,
        )
    else:
        await message.reply_text(
            f"ℹ️  <b>{bi('Sin tareas activas')}</b>\n\n"
            f"No tienes ninguna tarea en proceso ahora mismo.",
            parse_mode=PM,
        )


async def cmd_historial(app: Client, message: Message):
    if not await check_access(app, message):
        return
    uid = message.from_user.id
    rows = await get_history(uid, limit=10)
    if not rows:
        await message.reply_text(
            f"📋  <b>{bi('Historial vacío')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"No has subido ningún archivo aún.\n"
            f"¡Envíame algo para comenzar! 🚀",
            parse_mode=PM,
        )
        return

    lines = [
        f"📋  <b>{bi('Tus últimas subidas')}</b>",
        f"<code>{DIV}</code>",
        "",
    ]
    for i, (fname, link, size, created_at) in enumerate(rows, 1):
        lines.append(
            f"<b>{bi(str(i))}.</b>  {esc(fname[:40])}\n"
            f"     📦 {fmt_size(size)}  ·  📅 {created_at}\n"
            f"     <a href=\"{link}\">📥 Descargar</a>"
        )
    await message.reply_text(
        "\n\n".join(lines),
        parse_mode=PM,
        disable_web_page_preview=True,
    )




async def cmd_add_user(app: Client, message: Message):
    uid   = message.from_user.id
    uname = message.from_user.username
    if not is_admin(uid, uname):
        await message.reply_text(f"⛔  {bi('Solo el administrador puede usar este comando.')}", parse_mode=PM)
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        await message.reply_text(
            f"❓  <b>{bi('Uso:')}</b>\n\n"
            f"<code>/add_user [ID o @usuario]</code>\n\n"
            f"Ejemplos:\n  • <code>/add_user 123456789</code>\n  • <code>/add_user @nombre</code>",
            parse_mode=PM,
        )
        return

    raw = parts[1].strip().lstrip("@")
    try:
        entry = int(raw)
    except ValueError:
        entry = raw.lower()

    data = load_users()
    se = str(entry).lower()
    data["banned"] = [x for x in data["banned"] if str(x).lower() != se]
    if se not in [str(x).lower() for x in data["allowed"]]:
        data["allowed"].append(entry)
        save_users(data)
        await message.reply_text(
            f"✅  <b>{bi('Usuario Agregado')}</b>\n\n"
            f"👤  <code>{entry}</code>  ya tiene acceso al bot.",
            parse_mode=PM,
        )
        if isinstance(entry, int):
            try:
                await app.send_message(
                    entry,
                    f"✅  <b>{bi('¡Acceso Aprobado!')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"Ya puedes usar el bot.\n"
                    f"Envía /start para comenzar. 🚀",
                    parse_mode=PM,
                )
            except Exception:
                pass
    else:
        await message.reply_text(
            f"ℹ️  <code>{entry}</code> ya tiene acceso al bot.",
            parse_mode=PM,
        )


async def cmd_ban_user(app: Client, message: Message):
    uid   = message.from_user.id
    uname = message.from_user.username
    if not is_admin(uid, uname):
        await message.reply_text(f"⛔  {bi('Sin permiso.')}", parse_mode=PM)
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        await message.reply_text(
            f"❓  <b>{bi('Uso:')}</b>\n\n<code>/ban_user [ID o @usuario]</code>",
            parse_mode=PM,
        )
        return

    raw = parts[1].strip().lstrip("@")
    try:
        entry = int(raw)
    except ValueError:
        entry = raw.lower()

    if isinstance(entry, int) and _ADMIN_ID and entry == _ADMIN_ID:
        await message.reply_text(f"❌  {bi('No puedes banear al administrador.')}", parse_mode=PM)
        return

    data = load_users()
    se = str(entry).lower()
    data["allowed"] = [x for x in data["allowed"] if str(x).lower() != se]
    if se not in [str(x).lower() for x in data["banned"]]:
        data["banned"].append(entry)
        save_users(data)
        await message.reply_text(
            f"🚫  <b>{bi('Usuario Baneado')}</b>\n\n"
            f"👤  <code>{entry}</code>  ya no tiene acceso.",
            parse_mode=PM,
        )
    else:
        await message.reply_text(f"ℹ️  <code>{entry}</code> ya estaba baneado.", parse_mode=PM)


async def cmd_list_user(app: Client, message: Message):
    uid   = message.from_user.id
    uname = message.from_user.username
    if not is_admin(uid, uname):
        await message.reply_text(f"⛔  {bi('Sin permiso.')}", parse_mode=PM)
        return

    data = load_users()
    allowed = data.get("allowed", [])
    banned  = data.get("banned", [])

    def tag(u):
        adm = (isinstance(u, int) and _ADMIN_ID and u == _ADMIN_ID) or \
              (isinstance(u, str) and _ADMIN_USERNAME and u.lower() == _ADMIN_USERNAME)
        return f"  {'👑' if adm else '👤'}  <code>{u}</code>"

    allowed_lines = [tag(u) for u in allowed] if allowed else ["  —"]
    banned_lines  = [f"  🚫  <code>{u}</code>" for u in banned] if banned else ["  —"]

    lines = [
        f"👥  <b>{bi('Gestión de Usuarios')}</b>",
        f"<code>{DIV}</code>", "",
        f"✅  <b>Con acceso</b>  ({len(allowed)})",
        *allowed_lines, "",
        f"🚫  <b>Baneados</b>  ({len(banned)})",
        *banned_lines, "",
        f"<code>{DIV}</code>",
        f"📊  <b>Total:</b>  {len(allowed)} activos  ·  {len(banned)} baneados",
    ]
    await message.reply_text("\n".join(lines), parse_mode=PM)


async def cmd_cambiar_subida(app: Client, message: Message):
    """Cambia el destino de subida entre archive.org y el servidor local.
    Disponible para el admin y todos los usuarios aprobados."""
    if not await check_access(app, message):
        return

    parts = message.text.split(maxsplit=1)
    current = await get_upload_dest()

    # Sin argumento → muestra estado y botones
    if len(parts) < 2:
        cur_label = "💾 Servidor local" if current == "local" else "☁️ archive.org"
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("☁️ archive.org",    callback_data="dest_archive")],
            [InlineKeyboardButton("💾 Servidor local", callback_data="dest_local")],
        ])
        await message.reply_text(
            f"📤  <b>{bi('Destino de Subida')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"📍  Actual:  <b>{cur_label}</b>\n\n"
            f"<i>Selecciona el destino al que se subirán los archivos:</i>\n\n"
            f"  ☁️  <b>archive.org</b>  —  Almacenamiento público mundial\n"
            f"  💾  <b>Servidor local</b>  —  Sin gastar MB en Cuba si está\n"
            f"      detrás de un proxy nacional\n\n"
            f"<i>También puedes usar:</i>\n"
            f"<code>/cambiar_subida archive</code>  ó  <code>/cambiar_subida local</code>",
            parse_mode=PM,
            reply_markup=kb,
        )
        return

    arg = parts[1].strip().lower()
    if arg in ("archive", "archive.org", "nube", "cloud"):
        new_dest = "archive"
    elif arg in ("local", "servidor", "storage", "propio"):
        new_dest = "local"
    else:
        await message.reply_text(
            f"❓  <b>{bi('Uso:')}</b>\n\n"
            f"<code>/cambiar_subida archive</code>\n"
            f"<code>/cambiar_subida local</code>",
            parse_mode=PM,
        )
        return

    await set_upload_dest(new_dest)
    label = "💾 Servidor local" if new_dest == "local" else "☁️ archive.org"
    extra = ""
    if new_dest == "local":
        extra = (
            f"\n\n🌐  <b>URL pública:</b>\n"
            f"<code>{esc(STORAGE_PUBLIC_URL)}</code>\n\n"
            f"<i>Si está detrás de una pasarela cubana (.cu, proxy nacional),\n"
            f"las descargas no descontarán MB del paquete de internet.</i>"
        )
    await message.reply_text(
        f"✅  <b>{bi('Destino actualizado')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"📤  Nuevo destino:  <b>{label}</b>{extra}",
        parse_mode=PM,
        disable_web_page_preview=True,
    )


async def cmd_storage(app: Client, message: Message):
    """Muestra el estado del servidor de almacenamiento local."""
    if not await check_access(app, message):
        return
    uid   = message.from_user.id
    uname = message.from_user.username

    files = await list_storage_files()
    total = sum(f[2] for f in files)
    used_pct = (total / (STORAGE_MAX_GB * 1024 ** 3) * 100) if STORAGE_MAX_GB > 0 else 0
    cur_dest = await get_upload_dest()
    dest_label = "💾 Servidor local" if cur_dest == "local" else "☁️ archive.org"

    bar = progress_bar(used_pct)
    txt = (
        f"💾  <b>{bi('Servidor de Almacenamiento')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"📤  Destino actual:  <b>{dest_label}</b>\n"
        f"🌐  URL pública:\n<code>{esc(STORAGE_PUBLIC_URL)}</code>\n\n"
        f"📦  Archivos:  <b>{len(files)}</b>\n"
        f"💽  Usado:    <b>{fmt_size(total)}</b>  /  <b>{STORAGE_MAX_GB} GB</b>\n"
        f"<code>{bar}</code>  <b>{bi(f'{used_pct:.1f}%')}</b>\n\n"
        f"⏳  TTL por archivo:  "
        f"<b>{'sin caducidad' if STORAGE_FILE_TTL_DAYS == 0 else f'{STORAGE_FILE_TTL_DAYS} días'}</b>"
    )

    # Solo el admin ve el botón de borrado masivo
    kb = None
    if is_admin(uid, uname) and len(files) > 0:
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("🗑  Borrar todos los archivos", callback_data="storage_clear_ask")
        ]])

    await message.reply_text(txt, parse_mode=PM, disable_web_page_preview=True, reply_markup=kb)


async def cmd_set_cuota(app: Client, message: Message):
    uid   = message.from_user.id
    uname = message.from_user.username
    if not is_admin(uid, uname):
        await message.reply_text(f"⛔  {bi('Sin permiso.')}", parse_mode=PM)
        return

    parts = message.text.split()
    if len(parts) < 3:
        await message.reply_text(
            f"❓  <b>{bi('Uso:')}</b>\n\n"
            f"<code>/set_cuota [ID o @usuario] [límite_diario]</code>\n\n"
            f"Ejemplos:\n"
            f"  • <code>/set_cuota 123456789 20</code>\n"
            f"  • <code>/set_cuota @nombre 20</code>",
            parse_mode=PM,
        )
        return

    raw_target = parts[1].lstrip("@")
    try:
        limit = int(parts[2])
    except ValueError:
        await message.reply_text("❌  El límite debe ser un número entero.", parse_mode=PM)
        return

    # Resolver ID numérico o @usuario
    target_uid: int | None = None
    display = raw_target
    if raw_target.lstrip("-").isdigit():
        target_uid = int(raw_target)
    else:
        try:
            user_obj = await app.get_users(raw_target)
            target_uid = user_obj.id
            display = f"@{raw_target}"
        except Exception:
            await message.reply_text(
                f"❌  No se pudo encontrar al usuario <code>@{esc(raw_target)}</code>.\n\n"
                f"Asegúrate de que el usuario haya iniciado una conversación con el bot.",
                parse_mode=PM,
            )
            return

    await set_quota(target_uid, limit)
    await message.reply_text(
        f"✅  <b>{bi('Cuota actualizada')}</b>\n\n"
        f"👤  <code>{display}</code>\n"
        f"📊  Nueva cuota:  <b>{limit}</b> subidas/día",
        parse_mode=PM,
    )


# ─── Handlers de archivos y texto ─────────────────────────────────────────────

async def handle_file(app: Client, message: Message):
    if not await check_access(app, message):
        return
    uid   = message.from_user.id
    uname = message.from_user.username

    if not await check_quota(app, uid, uname, message.chat.id):
        return

    pos = await enqueue_job(app, uid, {
        "user_id":    uid,
        "chat_id":    message.chat.id,
        "username":   uname,
        "first_name": message.from_user.first_name or "",
        "type":       "file",
        "message":    message,
    })
    if pos > 0:
        await message.reply_text(
            f"📋  <b>{bi('En cola')}</b>\n\n"
            f"Tu archivo está en la posición  <b>{bi(str(pos + 1))}</b>.\n"
            f"Se procesará en cuanto termine la tarea anterior.",
            parse_mode=PM,
        )


async def handle_text(app: Client, message: Message):
    if not await check_access(app, message):
        return

    text = message.text or message.caption or ""
    url  = extract_url(text)

    if not url:
        await message.reply_text(
            f"💡  <b>{bi('¿Cómo usar el bot?')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"  📁  Envíame un archivo de Telegram  <i>(hasta 2 GB)</i>\n"
            f"  🎬  Enlace de YouTube o Playlist\n"
            f"  📸  Instagram · TikTok · Twitter/X\n"
            f"  🌐  Cualquier URL de descarga directa\n\n"
            f"<i>Escribe /help para ver todos los comandos.</i>",
            parse_mode=PM,
        )
        return

    uid   = message.from_user.id
    uname = message.from_user.username

    if not await check_quota(app, uid, uname, message.chat.id):
        return

    # Playlist de YouTube
    if is_youtube_playlist(url):
        key = str(uuid.uuid4())[:8]
        pending_playlist[key] = {
            "url": url, "user_id": uid, "chat_id": message.chat.id,
            "username": uname, "first_name": message.from_user.first_name or "",
        }
        await message.reply_text(
            f"🎵  <b>{bi('Playlist de YouTube detectada')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"🔗  <code>{esc(url[:70])}</code>\n\n"
            f"¿Qué deseas descargar?",
            parse_mode=PM,
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("📋 Toda la playlist", callback_data=f"playlist_all_{key}"),
                InlineKeyboardButton("🎬 Solo este video",  callback_data=f"playlist_one_{key}"),
            ]]),
        )
        return

    # Plataformas: selector de calidad
    if is_platform_url(url):
        key = str(uuid.uuid4())[:8]
        pending_quality[key] = {
            "url": url, "user_id": uid, "chat_id": message.chat.id,
            "username": uname, "first_name": message.from_user.first_name or "",
            "playlist": False,
        }
        await message.reply_text(
            f"🎬  <b>{bi('Selecciona la calidad')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"🔗  <code>{esc(url[:70])}</code>",
            parse_mode=PM,
            reply_markup=InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("⭐ Mejor calidad", callback_data=f"quality_best_{key}"),
                    InlineKeyboardButton("📺 1080p",         callback_data=f"quality_1080_{key}"),
                ],
                [
                    InlineKeyboardButton("📺 720p",          callback_data=f"quality_720_{key}"),
                    InlineKeyboardButton("📺 480p",          callback_data=f"quality_480_{key}"),
                ],
                [
                    InlineKeyboardButton("📺 360p",          callback_data=f"quality_360_{key}"),
                    InlineKeyboardButton("🎵 Solo audio",    callback_data=f"quality_audio_{key}"),
                ],
            ]),
        )
        return

    # URL directa
    pos = await enqueue_job(app, uid, {
        "user_id":    uid,
        "chat_id":    message.chat.id,
        "username":   uname,
        "first_name": message.from_user.first_name or "",
        "type":       "url",
        "url":        url,
    })
    if pos > 0:
        await message.reply_text(
            f"📋  <b>{bi(f'En cola — posición {pos + 1}')}</b>",
            parse_mode=PM,
        )


# ─── Búsqueda en Dailymotion ──────────────────────────────────────────────────

async def _dm_search_api(query: str, page: int = 1) -> dict:
    url = "https://api.dailymotion.com/videos"
    params = {
        "search":  query,
        "fields":  "id,title,url,duration",
        "limit":   DM_PER_PAGE,
        "page":    page,
        "sort":    "relevance",
    }
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as session:
            async with session.get(url, params=params) as resp:
                if resp.status != 200:
                    return {}
                return await resp.json()
    except Exception as e:
        logger.error(f"Dailymotion API error: {e}")
        return {}


def _fmt_dm_duration(seconds: int) -> str:
    if not seconds:
        return "—"
    m, s = divmod(int(seconds), 60)
    h, m = divmod(m, 60)
    if h:
        return f"{h}:{m:02d}:{s:02d}"
    return f"{m}:{s:02d}"


async def _send_dm_results(app: Client, chat_id: int, key: str, msg_id: int | None = None):
    state    = pending_dm_search.get(key)
    if not state:
        return
    results  = state["results"]
    page     = state["page"]
    total    = state["total"]
    query    = state["query"]
    has_more = state["has_more"]

    total_pages = (total + DM_PER_PAGE - 1) // DM_PER_PAGE if total else "?"

    lines = [
        f"🔍  <b>{bi('Dailymotion — Resultados')}</b>",
        f"<code>{DIV}</code>",
        f"🔎  <i>{esc(query)}</i>  ·  📄  Página {page}",
        "",
    ]
    buttons = []
    for idx, v in enumerate(results):
        title    = esc(v.get("title", "Sin título")[:55])
        dur      = _fmt_dm_duration(v.get("duration", 0))
        dm_url   = v.get("url", f"https://www.dailymotion.com/video/{v['id']}")
        num      = (page - 1) * DM_PER_PAGE + idx + 1
        lines.append(f"  <b>{num}.</b>  {title}  <code>[{dur}]</code>")
        lines.append(f"  🔗  <code>{dm_url}</code>")
        lines.append("")
        buttons.append([InlineKeyboardButton(
            f"⬇️  {num}. {v.get('title', 'Video')[:40]}",
            callback_data=f"dm_dl_{key}_{idx}",
        )])

    nav = []
    if page > 1:
        nav.append(InlineKeyboardButton("◀️ Anterior", callback_data=f"dm_pg_{key}_{page - 1}"))
    if has_more:
        nav.append(InlineKeyboardButton("Siguiente ▶️", callback_data=f"dm_pg_{key}_{page + 1}"))
    if nav:
        buttons.append(nav)

    text = "\n".join(lines)
    kb   = InlineKeyboardMarkup(buttons)

    if msg_id:
        await safe_edit(app, chat_id, msg_id, text, markup=kb)
    else:
        await app.send_message(chat_id, text, parse_mode=PM, reply_markup=kb)


async def cmd_buscar_dm(app: Client, message: Message):
    if not await check_access(app, message):
        return

    query = (message.text or "").strip()
    parts = query.split(None, 1)
    if len(parts) < 2 or not parts[1].strip():
        await message.reply_text(
            f"🔍  <b>{bi('Buscar en Dailymotion')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"<b>Uso:</b>  <code>/buscar_dm &lt;término de búsqueda&gt;</code>\n\n"
            f"<i>Ejemplo:</i>  <code>/buscar_dm documentales naturaleza</code>",
            parse_mode=PM,
        )
        return

    query = parts[1].strip()
    status = await message.reply_text(
        f"🔍  <b>{bi('Buscando en Dailymotion...')}</b>\n"
        f"<code>{DIV}</code>\n\n"
        f"🔎  <i>{esc(query)}</i>",
        parse_mode=PM,
    )

    data = await _dm_search_api(query, page=1)
    results = data.get("list", [])
    total   = data.get("total", 0)
    has_more = data.get("has_more", False)

    if not results:
        await safe_edit(
            app, message.chat.id, status.id,
            f"🔍  <b>{bi('Sin resultados')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"No se encontraron videos para: <i>{esc(query)}</i>",
        )
        return

    key = str(uuid.uuid4())[:8]
    pending_dm_search[key] = {
        "query":    query,
        "results":  results,
        "total":    total,
        "has_more": has_more,
        "page":     1,
        "user_id":  message.from_user.id,
        "chat_id":  message.chat.id,
    }

    await _send_dm_results(app, message.chat.id, key, msg_id=status.id)


# ─── Handler de callbacks ─────────────────────────────────────────────────────

async def handle_callback(app: Client, callback: CallbackQuery):
    data = callback.data or ""
    uid  = callback.from_user.id

    # Cancelar
    if data.startswith("cancel_"):
        try:
            task_uid = int(data.split("_", 1)[1])
        except ValueError:
            await callback.answer("Datos inválidos.", show_alert=True)
            return
        if uid != task_uid and not is_admin(uid, callback.from_user.username):
            await callback.answer("No tienes permiso.", show_alert=True)
            return
        task = active_tasks.get(task_uid)
        if task:
            task["cancel_event"].set()
            await callback.answer("⏹ Operación cancelada", show_alert=False)
            try:
                await callback.message.edit_text(
                    f"⏹  <b>{bi('Operación cancelada')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"La tarea fue detenida al instante.",
                    parse_mode=PM,
                )
            except Exception:
                pass
        else:
            await callback.answer("No hay tarea activa.", show_alert=True)
        return

    # Calidad
    if data.startswith("quality_"):
        parts = data.split("_", 2)
        if len(parts) < 3:
            await callback.answer("Datos inválidos.", show_alert=True)
            return
        quality, key = parts[1], parts[2]
        info = pending_quality.pop(key, None)
        if not info or info["user_id"] != uid:
            await callback.answer("Esta selección ya no es válida.", show_alert=True)
            return

        qlabel = QUALITY_LABELS.get(quality, quality)
        await callback.answer(f"✅ {qlabel}")
        try:
            await callback.message.delete()
        except Exception:
            pass

        pos = await enqueue_job(app, uid, {
            "user_id":    uid,
            "chat_id":    info["chat_id"],
            "username":   info["username"],
            "first_name": info["first_name"],
            "type":       "platform",
            "url":        info["url"],
            "quality":    quality,
            "playlist":   info.get("playlist", False),
        })
        if pos > 0:
            await app.send_message(
                info["chat_id"],
                f"📋  <b>{bi(f'En cola — posición {pos + 1}')}</b>",
                parse_mode=PM,
            )
        return

    # Playlist
    if data.startswith("playlist_"):
        parts = data.split("_", 2)
        if len(parts) < 3:
            await callback.answer("Datos inválidos.", show_alert=True)
            return
        mode, key = parts[1], parts[2]
        info = pending_playlist.pop(key, None)
        if not info or info["user_id"] != uid:
            await callback.answer("Esta selección ya no es válida.", show_alert=True)
            return

        playlist_mode = (mode == "all")
        await callback.answer("✅ Seleccionado")
        try:
            await callback.message.delete()
        except Exception:
            pass

        qual_key = str(uuid.uuid4())[:8]
        pending_quality[qual_key] = {
            "url":        info["url"],
            "user_id":    uid,
            "chat_id":    info["chat_id"],
            "username":   info["username"],
            "first_name": info["first_name"],
            "playlist":   playlist_mode,
        }
        await app.send_message(
            info["chat_id"],
            f"🎬  <b>{bi('Selecciona la calidad')}</b>\n"
            f"<code>{DIV}</code>",
            parse_mode=PM,
            reply_markup=InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("⭐ Mejor calidad", callback_data=f"quality_best_{qual_key}"),
                    InlineKeyboardButton("📺 1080p",         callback_data=f"quality_1080_{qual_key}"),
                ],
                [
                    InlineKeyboardButton("📺 720p",          callback_data=f"quality_720_{qual_key}"),
                    InlineKeyboardButton("📺 480p",          callback_data=f"quality_480_{qual_key}"),
                ],
                [
                    InlineKeyboardButton("📺 360p",          callback_data=f"quality_360_{qual_key}"),
                    InlineKeyboardButton("🎵 Solo audio",    callback_data=f"quality_audio_{qual_key}"),
                ],
            ]),
        )
        return

    # Borrar todos los archivos del servidor de almacenamiento
    if data == "storage_clear_ask":
        if not is_admin(uid, callback.from_user.username):
            await callback.answer("Solo el administrador puede hacer esto.", show_alert=True)
            return
        files = await list_storage_files()
        if not files:
            await callback.answer("No hay archivos que borrar.", show_alert=True)
            return
        total = sum(f[2] for f in files)
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("✅  Sí, borrar todo",   callback_data="storage_clear_yes")],
            [InlineKeyboardButton("✖  Cancelar",          callback_data="storage_clear_no")],
        ])
        try:
            await callback.message.edit_text(
                f"⚠️  <b>{bi('Confirmar borrado')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"Vas a borrar <b>{len(files)}</b> archivo(s)\n"
                f"liberando <b>{fmt_size(total)}</b>.\n\n"
                f"<i>Los enlaces previamente compartidos dejarán de funcionar.</i>\n"
                f"<b>Esta acción no se puede deshacer.</b>",
                parse_mode=PM,
                reply_markup=kb,
            )
        except Exception:
            pass
        await callback.answer()
        return

    if data == "storage_clear_no":
        if not is_admin(uid, callback.from_user.username):
            await callback.answer()
            return
        try:
            await callback.message.edit_text(
                f"✖  <b>{bi('Borrado cancelado')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"<i>No se eliminó ningún archivo.</i>",
                parse_mode=PM,
            )
        except Exception:
            pass
        await callback.answer("Cancelado")
        return

    if data == "storage_clear_yes":
        if not is_admin(uid, callback.from_user.username):
            await callback.answer("Solo el administrador puede hacer esto.", show_alert=True)
            return
        files = await list_storage_files()
        if not files:
            await callback.answer("No hay archivos que borrar.", show_alert=True)
            return
        await callback.answer("Borrando...")
        try:
            await callback.message.edit_text(
                f"🗑  <b>{bi('Borrando archivos...')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"<i>Esto puede tardar unos segundos.</i>",
                parse_mode=PM,
            )
        except Exception:
            pass
        deleted = 0
        freed = 0
        for ident, fname, size, _ts in files:
            try:
                if await delete_storage_file(ident):
                    deleted += 1
                    freed += size
            except Exception as e:
                logger.warning(f"No se pudo borrar {ident}: {e}")
        # Por si quedó algo huérfano en disco sin entrada en DB
        try:
            for entry in STORAGE_DIR.iterdir():
                if entry.is_dir():
                    shutil.rmtree(entry, ignore_errors=True)
        except Exception:
            pass
        try:
            await callback.message.edit_text(
                f"✅  <b>{bi('Servidor vaciado')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"🗑  Archivos borrados:  <b>{deleted}</b>\n"
                f"💽  Espacio liberado:  <b>{fmt_size(freed)}</b>\n\n"
                f"<i>Usa /storage para ver el estado actualizado.</i>",
                parse_mode=PM,
            )
        except Exception:
            pass
        return

    # Cambiar destino de subida (admin y usuarios aprobados)
    if data == "dest_archive" or data == "dest_local":
        if not is_allowed(uid, callback.from_user.username):
            await callback.answer("No tienes acceso al bot.", show_alert=True)
            return
        new_dest = "archive" if data == "dest_archive" else "local"
        await set_upload_dest(new_dest)
        label = "💾 Servidor local" if new_dest == "local" else "☁️ archive.org"
        await callback.answer(f"✅ Destino: {label}")
        try:
            extra = ""
            if new_dest == "local":
                extra = (
                    f"\n\n🌐  <b>URL pública:</b>\n"
                    f"<code>{esc(STORAGE_PUBLIC_URL)}</code>\n\n"
                    f"<i>Si está detrás de una pasarela cubana, las\n"
                    f"descargas no descontarán MB del paquete de internet.</i>"
                )
            await callback.message.edit_text(
                f"✅  <b>{bi('Destino actualizado')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"📤  Nuevo destino:  <b>{label}</b>{extra}",
                parse_mode=PM,
                disable_web_page_preview=True,
            )
        except Exception:
            pass
        return

    # Solicitud de acceso disparada por el botón "🔔 Pedir aprobación"
    if data.startswith("req_access_"):
        try:
            target_uid = int(data.split("_", 2)[2])
        except (ValueError, IndexError):
            await callback.answer("Datos inválidos.", show_alert=True)
            return
        # Solo el propio usuario puede pedir aprobación para sí mismo
        if target_uid != uid:
            await callback.answer("Este botón no es para ti.", show_alert=True)
            return
        # Si ya está aprobado, no tiene sentido reenviar
        if is_allowed(uid, callback.from_user.username):
            await callback.answer("✅ Ya tienes acceso al bot.", show_alert=True)
            return
        # Rate-limit: máximo 1 solicitud cada 10 minutos por usuario
        now = time.time()
        last = _ACCESS_REQ_COOLDOWN.get(uid, 0)
        if now - last < 600:
            faltan = int(600 - (now - last))
            mins = faltan // 60
            secs = faltan % 60
            await callback.answer(
                f"⏳ Espera {mins}m {secs}s antes de pedir de nuevo.",
                show_alert=True,
            )
            return
        if not _ADMIN_ID:
            await callback.answer("No hay administrador configurado.", show_alert=True)
            return
        fname = callback.from_user.first_name or "Usuario"
        uname_str = callback.from_user.username
        baneado = is_banned(uid, uname_str)
        try:
            await app.send_message(
                _ADMIN_ID,
                f"🔔  <b>{bi('Solicitud de Acceso')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"👤  <b>{esc(fname)}</b>\n"
                f"🆔  <code>{uid}</code>\n"
                f"📧  @{esc(uname_str or 'sin_usuario')}\n"
                + (f"\n⚠️  <i>Este usuario está actualmente baneado.</i>\n" if baneado else "")
                + f"\n<i>El usuario tocó el botón «Pedir aprobación».</i>",
                parse_mode=PM,
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("✅ Aprobar",  callback_data=f"approve_{uid}"),
                    InlineKeyboardButton("❌ Rechazar", callback_data=f"reject_{uid}"),
                ]]),
            )
        except Exception as e:
            logger.warning(f"No se pudo notificar al admin (req_access): {e}")
            await callback.answer("No se pudo enviar la solicitud.", show_alert=True)
            return
        _ACCESS_REQ_COOLDOWN[uid] = now
        await callback.answer("✅ Solicitud enviada al administrador.", show_alert=True)
        # Reemplaza el botón para evitar spam visual
        try:
            await callback.message.edit_reply_markup(
                InlineKeyboardMarkup([
                    [InlineKeyboardButton("✉️ Solicitud enviada · espera respuesta", callback_data="noop")],
                    [InlineKeyboardButton("📩 Contactar Administrador", url=admin_contact_url())],
                ])
            )
        except Exception:
            pass
        return

    if data == "noop":
        await callback.answer()
        return

    # Aprobar / Rechazar acceso
    if data.startswith("approve_") or data.startswith("reject_"):
        if not is_admin(uid, callback.from_user.username):
            await callback.answer("Solo el administrador puede hacer esto.", show_alert=True)
            return

        action, target_str = data.split("_", 1)
        try:
            target_uid = int(target_str)
        except ValueError:
            await callback.answer("Datos inválidos.", show_alert=True)
            return

        if action == "approve":
            data_users = load_users()
            se = str(target_uid)
            data_users["banned"] = [x for x in data_users["banned"] if str(x) != se]
            if target_uid not in data_users["allowed"]:
                data_users["allowed"].append(target_uid)
                save_users(data_users)

            await callback.answer("✅ Usuario aprobado")
            try:
                await callback.message.edit_text(
                    callback.message.text + "\n\n✅  <b>Aprobado por el administrador.</b>",
                    parse_mode=PM,
                )
            except Exception:
                pass
            try:
                await app.send_message(
                    target_uid,
                    f"✅  <b>{bi('¡Acceso Aprobado!')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"Ya puedes usar el bot.\n"
                    f"Envía /start para comenzar. 🚀",
                    parse_mode=PM,
                )
            except Exception:
                pass
        else:
            await callback.answer("❌ Solicitud rechazada")
            try:
                await callback.message.edit_text(
                    callback.message.text + "\n\n❌  <b>Rechazado por el administrador.</b>",
                    parse_mode=PM,
                )
            except Exception:
                pass
            try:
                await app.send_message(
                    target_uid,
                    f"❌  <b>{bi('Solicitud Rechazada')}</b>\n"
                    f"<code>{DIV}</code>\n\n"
                    f"El administrador ha rechazado tu solicitud de acceso.",
                    parse_mode=PM,
                    reply_markup=admin_contact_btn(target_uid),
                )
            except Exception:
                pass
        return

    # ── Dailymotion: página siguiente / anterior ───────────────────────────────
    if data.startswith("dm_pg_"):
        parts = data.split("_")
        if len(parts) < 4:
            await callback.answer("Datos inválidos.", show_alert=True)
            return
        key  = parts[2]
        try:
            new_page = int(parts[3])
        except ValueError:
            await callback.answer("Datos inválidos.", show_alert=True)
            return

        state = pending_dm_search.get(key)
        if not state or state["user_id"] != uid:
            await callback.answer("Esta búsqueda ya no está disponible.", show_alert=True)
            return

        await callback.answer(f"📄 Cargando página {new_page}...")

        loading_text = (
            f"🔍  <b>{bi('Dailymotion — Resultados')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"⏳  {bi(f'Cargando página {new_page}...')}"
        )
        try:
            await callback.message.edit_text(loading_text, parse_mode=PM)
        except Exception:
            pass

        dm_data = await _dm_search_api(state["query"], page=new_page)
        results  = dm_data.get("list", [])
        if not results:
            await safe_edit(
                app, state["chat_id"], callback.message.id,
                f"🔍  <b>{bi('Sin más resultados')}</b>\n"
                f"<code>{DIV}</code>\n\n"
                f"No hay más videos en esta página.",
            )
            return

        state["results"]  = results
        state["page"]     = new_page
        state["total"]    = dm_data.get("total", state["total"])
        state["has_more"] = dm_data.get("has_more", False)

        await _send_dm_results(app, state["chat_id"], key, msg_id=callback.message.id)
        return

    # ── Dailymotion: descargar video seleccionado ──────────────────────────────
    if data.startswith("dm_dl_"):
        parts = data.split("_")
        if len(parts) < 4:
            await callback.answer("Datos inválidos.", show_alert=True)
            return
        key = parts[2]
        try:
            idx = int(parts[3])
        except ValueError:
            await callback.answer("Datos inválidos.", show_alert=True)
            return

        state = pending_dm_search.get(key)
        if not state or state["user_id"] != uid:
            await callback.answer("Esta búsqueda ya no está disponible.", show_alert=True)
            return

        results = state.get("results", [])
        if idx >= len(results):
            await callback.answer("Video no encontrado.", show_alert=True)
            return

        video    = results[idx]
        dm_url   = video.get("url", f"https://www.dailymotion.com/video/{video['id']}")
        title    = video.get("title", "Video")

        await callback.answer("✅ Iniciando selección de calidad...")

        qual_key = str(uuid.uuid4())[:8]
        pending_quality[qual_key] = {
            "url":        dm_url,
            "user_id":    uid,
            "chat_id":    state["chat_id"],
            "username":   callback.from_user.username,
            "first_name": callback.from_user.first_name or "",
            "playlist":   False,
        }
        await app.send_message(
            state["chat_id"],
            f"🎬  <b>{bi('Selecciona la calidad')}</b>\n"
            f"<code>{DIV}</code>\n\n"
            f"📹  <i>{esc(title[:70])}</i>\n"
            f"🔗  <code>{dm_url}</code>",
            parse_mode=PM,
            reply_markup=InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("⭐ Mejor calidad", callback_data=f"quality_best_{qual_key}"),
                    InlineKeyboardButton("📺 1080p",         callback_data=f"quality_1080_{qual_key}"),
                ],
                [
                    InlineKeyboardButton("📺 720p",          callback_data=f"quality_720_{qual_key}"),
                    InlineKeyboardButton("📺 480p",          callback_data=f"quality_480_{qual_key}"),
                ],
                [
                    InlineKeyboardButton("📺 360p",          callback_data=f"quality_360_{qual_key}"),
                    InlineKeyboardButton("🎵 Solo audio",    callback_data=f"quality_audio_{qual_key}"),
                ],
            ]),
        )
        return

    await callback.answer()


# ─── Servidor Web (salud + almacenamiento de descargas) ──────────────────────
#
# Sirve en el mismo puerto:
#   GET /                       → "OK" (health-check)
#   GET /d/<sig>/<id>/<file>    → archivo (Range, ETag, Last-Modified, If-Range)
#   GET /info/<sig>/<id>/<file> → JSON con metadatos del archivo (gzip)
#   GET /m/<sig>/<id>/<file>    → manifest mínimo cacheable (sha256 + mirrors)
#
# Funciones de robustez para minimizar el consumo de MB en redes caras:
#   • HTTP Range  → permite reanudar descargas (no se reenvían bytes ya bajados)
#   • If-Range    → si el archivo cambió, devuelve 200 completo (NO concatena
#                   bytes nuevos al final de bytes viejos = no malgasta MB)
#   • ETag (sha1 corto) + If-None-Match  → 304 Not Modified si no cambió
#   • Last-Modified + If-Modified-Since  → 304 Not Modified
#   • Cache-Control immutable (1 año)    → navegador y proxies cachean
#   • Accept-Ranges: bytes               → indica soporte de reanudación
#   • Digest: sha-256=...  + X-Content-SHA256  → integridad verificable sin
#                   tener que volver a descargar el archivo
#   • Manifest /m/...  → JSON ~200 B con sha256 + lista de mirrors. El cliente
#                   lo guarda y elige el mirror más barato (p.ej. .cu en Cuba)
#   • Vary: Accept-Encoding              → cachés intermedios bien-formados
#   • Content-Disposition con UTF-8      → preserva el nombre original
#   • Conexión HTTP/1.1 keep-alive       → ahorra handshakes TLS
#   • STORAGE_MIRRORS env  → lista de bases alternativas (proxy cubano, CDN…)
#

def _safe_resolve_storage(identifier: str, filename: str) -> Path | None:
    """Resuelve el archivo evitando path traversal."""
    try:
        base   = STORAGE_DIR.resolve()
        target = (STORAGE_DIR / identifier / filename).resolve()
        if not str(target).startswith(str(base) + os.sep):
            return None
        if not target.is_file():
            return None
        return target
    except Exception:
        return None


def _file_etag(path: Path) -> str:
    st = path.stat()
    raw = f"{path.name}:{st.st_size}:{int(st.st_mtime)}"
    return '"' + hashlib.sha1(raw.encode()).hexdigest()[:16] + '"'


async def _handle_health(_request: aioweb.Request) -> aioweb.Response:
    return aioweb.Response(text="OK", content_type="text/plain")


async def _handle_storage_info(request: aioweb.Request) -> aioweb.Response:
    sig        = request.match_info.get("sig", "")
    identifier = request.match_info.get("identifier", "")
    filename   = request.match_info.get("filename", "")
    expected   = _sign_path(f"{identifier}/{filename}")
    if not hmac.compare_digest(sig, expected):
        return aioweb.Response(status=403, text="Firma inválida")
    target = _safe_resolve_storage(identifier, filename)
    if not target:
        return aioweb.Response(status=404, text="Archivo no encontrado")
    st       = target.stat()
    sha256   = await get_storage_sha256(identifier)
    urls     = _make_storage_links(identifier, filename)
    resp = aioweb.json_response({
        "filename":   filename,
        "size":       st.st_size,
        "size_h":     fmt_size(st.st_size),
        "mtime":      int(st.st_mtime),
        "etag":       _file_etag(target).strip('"'),
        "sha256":     sha256,
        "url":        urls[0],
        "mirrors":    urls[1:],
        "manifest":   _make_manifest_link(identifier, filename),
        "supports": {
            "range":          True,
            "if_range":       True,
            "if_none_match":  True,
            "if_modified_since": True,
            "head":           True,
        },
    })
    resp.headers["Cache-Control"] = "public, max-age=60"
    resp.enable_compression()
    return resp


async def _handle_storage_manifest(request: aioweb.Request) -> aioweb.Response:
    """Manifest mínimo (~200 B) cacheable para siempre.

    Idea: el cliente descarga este JSON una sola vez y lo guarda; en futuras
    sesiones puede verificar integridad por sha256 sin reenviar el archivo,
    y elegir el mirror más barato. El manifest sí se sirve con gzip."""
    sig        = request.match_info.get("sig", "")
    identifier = request.match_info.get("identifier", "")
    filename   = request.match_info.get("filename", "")
    expected   = _sign_path(f"{identifier}/{filename}")
    if not hmac.compare_digest(sig, expected):
        return aioweb.Response(status=403, text="Firma inválida")
    target = _safe_resolve_storage(identifier, filename)
    if not target:
        return aioweb.Response(status=404, text="Archivo no encontrado")
    st     = target.stat()
    sha256 = await get_storage_sha256(identifier)
    urls   = _make_storage_links(identifier, filename)
    body = {
        "v":        1,
        "name":     filename,
        "size":     st.st_size,
        "etag":     _file_etag(target).strip('"'),
        "sha256":   sha256,           # puede ser null mientras se calcula
        "urls":     urls,
        "chunk":    STORAGE_SERVE_CHUNK,
    }
    resp = aioweb.json_response(body)
    # Si ya tenemos sha256, el manifest es inmutable (el contenido nunca cambia)
    if sha256:
        resp.headers["Cache-Control"] = "public, max-age=31536000, immutable"
        resp.headers["ETag"] = '"m-' + sha256[:16] + '"'
    else:
        resp.headers["Cache-Control"] = "public, max-age=30, stale-while-revalidate=300"
    resp.headers["Vary"] = "Accept-Encoding"
    resp.enable_compression()
    return resp


async def _handle_storage_download(request: aioweb.Request) -> aioweb.StreamResponse:
    sig        = request.match_info.get("sig", "")
    identifier = request.match_info.get("identifier", "")
    filename   = request.match_info.get("filename", "")

    # Verificación del enlace firmado
    expected = _sign_path(f"{identifier}/{filename}")
    if not hmac.compare_digest(sig, expected):
        return aioweb.Response(status=403, text="Firma inválida")

    target = _safe_resolve_storage(identifier, filename)
    if not target:
        return aioweb.Response(status=404, text="Archivo no encontrado")

    st         = target.stat()
    total_size = st.st_size
    etag       = _file_etag(target)
    last_mod   = time.strftime("%a, %d %b %Y %H:%M:%S GMT", time.gmtime(st.st_mtime))

    base_headers = {
        "Accept-Ranges":  "bytes",
        "ETag":            etag,
        "Last-Modified":   last_mod,
        "Cache-Control":   "public, max-age=31536000, immutable",
        "X-Content-Type-Options": "nosniff",
        "Vary":            "Accept-Encoding",
    }

    # 304 Not Modified — ahorra el 100% del cuerpo de la respuesta
    inm = request.headers.get("If-None-Match", "")
    if inm and etag in [t.strip() for t in inm.split(",")]:
        return aioweb.Response(status=304, headers=base_headers)
    ims = request.headers.get("If-Modified-Since", "")
    if ims:
        try:
            t_ims = time.mktime(time.strptime(ims, "%a, %d %b %Y %H:%M:%S GMT"))
            if int(st.st_mtime) <= int(t_ims):
                return aioweb.Response(status=304, headers=base_headers)
        except Exception:
            pass

    # Determinar tipo de contenido
    ctype, _ = mimetypes.guess_type(filename)
    if not ctype:
        ctype = "application/octet-stream"

    # Cabecera de nombre de archivo con compatibilidad UTF-8 (RFC 5987)
    safe_ascii = re.sub(r"[^\w\.-]", "_", filename)
    cd_value   = f"attachment; filename=\"{safe_ascii}\"; filename*=UTF-8''{quote(filename)}"

    # Procesar Range (reanudación)
    rng = request.headers.get("Range", "").strip()
    start, end = 0, total_size - 1
    status_code = 200

    # If-Range: si el cliente reanuda con un validador (ETag o fecha) que YA NO
    # coincide con el archivo actual, debemos enviar 200 con el archivo completo,
    # no 206 — de lo contrario pegaríamos bytes nuevos al final de bytes viejos
    # y arruinaríamos la descarga (gastando MB para nada).
    if_range = request.headers.get("If-Range", "").strip()
    range_valid = True
    if rng and if_range:
        if if_range.startswith('"') or if_range.startswith("W/"):
            # Validador por ETag
            if if_range != etag:
                range_valid = False
        else:
            # Validador por fecha HTTP
            try:
                t_ifr = time.mktime(time.strptime(if_range, "%a, %d %b %Y %H:%M:%S GMT"))
                if int(st.st_mtime) > int(t_ifr):
                    range_valid = False
            except Exception:
                range_valid = False

    if rng.startswith("bytes=") and range_valid:
        try:
            spec = rng[6:].split(",")[0].strip()
            if "-" in spec:
                a, b = spec.split("-", 1)
                if a == "":   # sufijo: bytes=-N
                    n = int(b)
                    start = max(0, total_size - n)
                else:
                    start = int(a)
                    end   = int(b) if b else total_size - 1
                if start > end or start >= total_size:
                    return aioweb.Response(
                        status=416,
                        headers={**base_headers, "Content-Range": f"bytes */{total_size}"},
                    )
                end = min(end, total_size - 1)
                status_code = 206
        except Exception:
            start, end, status_code = 0, total_size - 1, 200

    length = end - start + 1

    headers = {
        **base_headers,
        "Content-Type":        ctype,
        "Content-Length":      str(length),
        "Content-Disposition": cd_value,
    }
    if status_code == 206:
        headers["Content-Range"] = f"bytes {start}-{end}/{total_size}"

    # Cabecera de integridad (RFC 3230) — solo en respuestas completas
    if status_code == 200:
        sha256_hex = await get_storage_sha256(identifier)
        if sha256_hex:
            try:
                digest_b64 = base64.b64encode(bytes.fromhex(sha256_hex)).decode("ascii")
                headers["Digest"] = f"sha-256={digest_b64}"
                headers["X-Content-SHA256"] = sha256_hex
            except Exception:
                pass

    resp = aioweb.StreamResponse(status=status_code, headers=headers)
    await resp.prepare(request)

    # HEAD → solo cabeceras
    if request.method == "HEAD":
        return resp

    # Streaming sin buffer adicional, en chunks pequeños — minimiza memoria
    try:
        async with aiofiles.open(str(target), "rb") as f:
            await f.seek(start)
            remaining = length
            while remaining > 0:
                chunk = await f.read(min(STORAGE_SERVE_CHUNK, remaining))
                if not chunk:
                    break
                try:
                    await resp.write(chunk)
                except (ConnectionResetError, asyncio.CancelledError):
                    # El cliente cerró la conexión → no contabilizar más MB
                    return resp
                remaining -= len(chunk)
        await resp.write_eof()
    except Exception as e:
        logger.warning(f"Storage: error sirviendo {identifier}/{filename}: {e}")
    return resp


def build_web_app() -> aioweb.Application:
    web_app = aioweb.Application(
        client_max_size=2 * 1024 ** 3,  # 2 GB
    )
    # add_get registra GET y HEAD automáticamente
    web_app.router.add_get("/", _handle_health)
    web_app.router.add_get(
        "/d/{sig}/{identifier}/{filename}",
        _handle_storage_download,
    )
    web_app.router.add_get(
        "/info/{sig}/{identifier}/{filename}",
        _handle_storage_info,
    )
    web_app.router.add_get(
        "/m/{sig}/{identifier}/{filename}",
        _handle_storage_manifest,
    )
    return web_app


_web_runner: aioweb.AppRunner | None = None


async def start_web_server():
    """Inicia aiohttp en el mismo loop asyncio que Pyrogram."""
    global _web_runner
    web_app = build_web_app()
    runner  = aioweb.AppRunner(web_app, access_log=None)
    await runner.setup()
    last_err = None
    for attempt in range(5):
        try:
            site = aioweb.TCPSite(runner, "0.0.0.0", HEALTH_PORT)
            await site.start()
            _web_runner = runner
            logger.info(
                f"Servidor web/almacenamiento en puerto {HEALTH_PORT} "
                f"(URL pública: {STORAGE_PUBLIC_URL})"
            )
            return
        except OSError as e:
            last_err = e
            await asyncio.sleep(2)
    logger.warning(f"Servidor web no disponible en puerto {HEALTH_PORT}: {last_err}")


async def stop_web_server():
    global _web_runner
    if _web_runner:
        try:
            await _web_runner.cleanup()
        except Exception:
            pass
        _web_runner = None


# ─── Main ─────────────────────────────────────────────────────────────────────

def _validate_config() -> list[str]:
    errors = []
    # Token de Telegram: formato "123456:ABCdef..." (id numérico + ":" + hash)
    _token_parts = BOT_TOKEN.split(":", 1)
    if not BOT_TOKEN or len(_token_parts) != 2 or not _token_parts[0].isdigit() or len(_token_parts[1]) < 10:
        errors.append("TELEGRAM_BOT_TOKEN — falta o tiene valor de ejemplo")
    if not API_ID:
        errors.append("TELEGRAM_API_ID — falta o no es un número válido")
    if not API_HASH or len(API_HASH) < 10:
        errors.append("TELEGRAM_API_HASH — falta o tiene valor de ejemplo")
    if not ARCHIVE_ACCESS or len(ARCHIVE_ACCESS) < 10:
        errors.append("ARCHIVE_ORG_ACCESS_KEY — falta o tiene valor de ejemplo")
    if not ARCHIVE_SECRET or len(ARCHIVE_SECRET) < 10:
        errors.append("ARCHIVE_ORG_SECRET_KEY — falta o tiene valor de ejemplo")
    return errors


async def main():
    await init_db()

    config_errors = _validate_config()
    if config_errors:
        logger.error("=" * 60)
        logger.error("❌ ERROR: Variables de entorno no configuradas:")
        for e in config_errors:
            logger.error(f"   • {e}")
        logger.error("Por favor rellena el archivo .env con tus credenciales reales.")
        logger.error("=" * 60)
        return

    await start_web_server()
    await _enforce_storage_quota()

    app = Client(
        "bot_session",
        api_id=API_ID,
        api_hash=API_HASH,
        bot_token=BOT_TOKEN,
        workdir=str(Path(__file__).parent),
    )

    # Comandos
    app.on_message(filters.command("start")     & filters.private)(cmd_start)
    app.on_message(filters.command("help")      & filters.private)(cmd_help)
    app.on_message(filters.command("status")    & filters.private)(cmd_status)
    app.on_message(filters.command("cancelar")  & filters.private)(cmd_cancelar)
    app.on_message(filters.command("historial") & filters.private)(cmd_historial)
    app.on_message(filters.command("add_user")  & filters.private)(cmd_add_user)
    app.on_message(filters.command("ban_user")  & filters.private)(cmd_ban_user)
    app.on_message(filters.command("list_user") & filters.private)(cmd_list_user)
    app.on_message(filters.command("set_cuota")  & filters.private)(cmd_set_cuota)
    app.on_message(filters.command("cambiar_subida") & filters.private)(cmd_cambiar_subida)
    app.on_message(filters.command("storage")    & filters.private)(cmd_storage)
    app.on_message(filters.command("buscar_dm") & filters.private)(cmd_buscar_dm)

    # Archivos (MTProto — hasta 2 GB)
    app.on_message(
        filters.private & (
            filters.document | filters.video | filters.audio |
            filters.voice | filters.video_note | filters.animation | filters.photo
        )
    )(handle_file)

    # Texto y URLs
    app.on_message(
        filters.private & filters.text
        & ~filters.command([
            "start", "help", "status", "cancelar", "historial",
            "add_user", "ban_user", "list_user", "set_cuota",
            "cambiar_subida", "storage", "buscar_dm",
        ])
    )(handle_text)

    # Callbacks
    app.on_callback_query()(handle_callback)

    logger.info("Iniciando bot con Pyrogram (MTProto)...")
    await app.start()

    # Comandos para usuarios normales (barra de Telegram)
    user_commands = [
        BotCommand("start",          "🤖 Inicio y bienvenida"),
        BotCommand("help",           "📋 Comandos disponibles"),
        BotCommand("status",         "⚙️ Estado de tu tarea actual"),
        BotCommand("cancelar",       "⏹ Cancelar tarea en curso"),
        BotCommand("historial",      "📂 Tus últimas 10 subidas"),
        BotCommand("buscar_dm",      "🔍 Buscar videos en Dailymotion"),
        BotCommand("cambiar_subida", "📤 Cambiar destino de subida"),
        BotCommand("storage",        "💾 Estado del servidor de almacenamiento"),
    ]
    await app.set_bot_commands(user_commands, scope=BotCommandScopeDefault())

    # Comandos exclusivos para el administrador
    admin_chat_id: int | str | None = _ADMIN_ID or (f"@{_ADMIN_USERNAME}" if _ADMIN_USERNAME else None)
    if admin_chat_id:
        admin_commands = user_commands + [
            BotCommand("add_user",       "👤 Agregar usuario"),
            BotCommand("ban_user",       "🚫 Banear usuario"),
            BotCommand("list_user",      "👥 Ver todos los usuarios"),
            BotCommand("set_cuota",      "📊 Cambiar cuota diaria"),
        ]
        try:
            await app.set_bot_commands(admin_commands, scope=BotCommandScopeChat(chat_id=admin_chat_id))
        except Exception as e:
            logger.warning(f"No se pudieron registrar comandos de admin: {e}")

    logger.info("✅ Bot v3.1 iniciado — listo para recibir mensajes")
    try:
        await idle()
    finally:
        await app.stop()
        await stop_web_server()


if __name__ == "__main__":
    asyncio.run(main())
