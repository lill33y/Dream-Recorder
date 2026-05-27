"""
梦境记录：邮箱注册（验证码）、找回密码、头像、梦境颜色与单行历史预览。
发信（任选其一，用于真实邮箱验证码与重置密码链接）：
  - 推荐：RESEND_API_KEY + RESEND_FROM（HTTPS，见 https://resend.com ）
  - 或：SMTP_HOST, SMTP_PORT, SMTP_USER, SMTP_PASSWORD, SMTP_FROM；
    端口 465 或设置 SMTP_SSL=1 时使用 SSL；SMTP_USE_TLS=0 可关闭 STARTTLS（587 少数邮局需要）。
未配置发信时验证码仍会写入数据库并打印在运行 Flask 的终端日志中，但用户邮箱收不到。
BASE_URL 用于重置密码链接（默认同请求域名）。
梦境 AI 分析（可选）：优先 DEEPSEEK_API_KEY（官方 API，.env 中配置）；
可选 DEEPSEEK_MODEL（默认 deepseek-chat）。若未配置 DeepSeek，则回退 OPENROUTER_API_KEY 等。
展示时间：APP_TIMEZONE（默认 Asia/Shanghai），将 UTC 的 created_at 转为本地显示。
"""
import json
import logging
import os
import re
import secrets
import smtplib
import sqlite3
import urllib.error
import urllib.request
import uuid
from urllib.parse import quote
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from functools import wraps
from pathlib import Path
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

from flask import (
    Flask,
    flash,
    jsonify,
    redirect,
    render_template,
    request,
    session,
    url_for,
)
from dotenv import load_dotenv
from werkzeug.security import check_password_hash, generate_password_hash
from werkzeug.utils import secure_filename

APP_DIR = Path(__file__).resolve().parent
load_dotenv(APP_DIR / ".env")
DB_PATH = APP_DIR / "dreams.db"
UPLOAD_ROOT = APP_DIR / "static" / "user_audio"
AVATAR_ROOT = APP_DIR / "static" / "user_avatars"
ALLOWED_AUDIO_EXT = {".webm", ".wav", ".mp3", ".m4a", ".ogg", ".opus"}
ALLOWED_AVATAR_EXT = {".jpg", ".jpeg", ".png", ".gif", ".webp"}
# 梦境颜色：仅允许下列 20 种（保存时校验）；展示时仍兼容旧数据中的任意合法 #RRGGBB。
DEFAULT_DREAM_COLOR = "#87ceeb"

DREAM_COLOR_PALETTE: list[dict[str, str]] = [
    {"emotion": "愤怒", "color_zh": "红色", "hex": "#ff0000"},
    {"emotion": "悲伤", "color_zh": "深蓝色", "hex": "#00008b"},
    {"emotion": "焦虑", "color_zh": "柠檬黄", "hex": "#ffff00"},
    {"emotion": "平静", "color_zh": "淡绿色", "hex": "#90ee90"},
    {"emotion": "忧郁", "color_zh": "深紫色", "hex": "#800080"},
    {"emotion": "急躁", "color_zh": "亮橙色", "hex": "#ff8c00"},
    {"emotion": "喜悦", "color_zh": "明黄色", "hex": "#ffd700"},
    {"emotion": "惊讶", "color_zh": "亮粉色", "hex": "#ff69b4"},
    {"emotion": "恐惧", "color_zh": "深灰色", "hex": "#333333"},
    {"emotion": "嫉妒", "color_zh": "暗绿色", "hex": "#006400"},
    {"emotion": "疲惫", "color_zh": "浅棕色", "hex": "#c4a574"},
    {"emotion": "满足", "color_zh": "暖橙色", "hex": "#ffa500"},
    {"emotion": "孤独", "color_zh": "淡紫色", "hex": "#e6e6fa"},
    {"emotion": "期待", "color_zh": "浅蓝色", "hex": "#87ceeb"},
    {"emotion": "自豪", "color_zh": "金色", "hex": "#e6b422"},
    {"emotion": "愧疚", "color_zh": "暗紫色", "hex": "#4b0082"},
    {"emotion": "害羞", "color_zh": "浅粉色", "hex": "#ffb6c1"},
    {"emotion": "困惑", "color_zh": "蓝绿色", "hex": "#008080"},
    {"emotion": "怀念", "color_zh": "米黄色", "hex": "#f5f5dc"},
    {"emotion": "释然", "color_zh": "淡青色", "hex": "#e0ffff"},
]

ALLOWED_DREAM_HEX = frozenset(entry["hex"] for entry in DREAM_COLOR_PALETTE)

OTP_TTL_MINUTES = 15
RESET_TOKEN_TTL_HOURS = 2
OPENROUTER_URL = "https://openrouter.ai/api/v1/chat/completions"
OPENROUTER_DEFAULT_MODEL = "openai/gpt-4o-mini"
DEEPSEEK_URL = "https://api.deepseek.com/v1/chat/completions"
DEEPSEEK_DEFAULT_MODEL = "deepseek-chat"
MAX_DREAM_CHARS_FOR_ANALYSIS = 20000

logger = logging.getLogger(__name__)


def _display_zoneinfo():
    tzname = (os.environ.get("APP_TIMEZONE") or "Asia/Shanghai").strip()
    try:
        return ZoneInfo(tzname)
    except ZoneInfoNotFoundError:
        return ZoneInfo("Asia/Shanghai")


def parse_iso_datetime(iso_s: str):
    if not iso_s:
        return None
    try:
        dt = datetime.fromisoformat(iso_s.replace("Z", "+00:00"))
    except ValueError:
        return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt


def format_display_datetime(iso_s: str) -> str:
    dt = parse_iso_datetime(iso_s)
    if not dt:
        return (iso_s or "")[:19]
    local = dt.astimezone(_display_zoneinfo())
    return local.strftime("%Y年%m月%d日 %H:%M")


def local_date_str_from_iso(iso_s: str) -> str:
    dt = parse_iso_datetime(iso_s)
    if not dt:
        return datetime.now(_display_zoneinfo()).strftime("%Y-%m-%d")
    return dt.astimezone(_display_zoneinfo()).strftime("%Y-%m-%d")


def parse_dream_on_field(raw: str) -> str | None:
    s = (raw or "").strip()
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", s):
        return s
    return None


def get_db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def utc_now():
    return datetime.now(timezone.utc)


def utc_now_iso():
    return utc_now().isoformat()


def normalize_email(email: str) -> str:
    return (email or "").strip().lower()


def is_valid_email(email: str) -> bool:
    if not email or "@" not in email or len(email) > 254:
        return False
    local, _, domain = email.partition("@")
    if len(local) > 64 or len(domain) < 1 or "." not in domain:
        return False
    return bool(re.match(r"^[^\s@]+$", local) and re.match(r"^[^\s@]+\.[^\s@]+$", domain))


def sanitize_hex_color(value: str) -> str:
    """展示用：任意合法 #RRGGBB 原样返回（兼容旧记录），否则回退默认色。"""
    s = (value or "").strip()
    if re.fullmatch(r"#[0-9a-fA-F]{6}", s):
        return s.lower()
    return DEFAULT_DREAM_COLOR


def dream_color_for_save(value: str) -> str:
    """新写入梦境时仅允许调色板中的 20 种颜色。"""
    s = (value or "").strip().lower()
    if s in ALLOWED_DREAM_HEX:
        return s
    return DEFAULT_DREAM_COLOR


def sanitize_nickname(value: str, fallback: str) -> str:
    s = re.sub(r"[\x00-\x1f\x7f]", "", (value or "").strip())
    fb = (fallback or "旅人").strip() or "旅人"
    if not s:
        s = fb
    if len(s) > 24:
        s = s[:24]
    return s


def _strip_llm_json_fence(text: str) -> str:
    s = (text or "").strip()
    if not s.startswith("```"):
        return s
    s = re.sub(r"^```(?:json)?\s*", "", s, flags=re.IGNORECASE)
    s = re.sub(r"\s*```\s*$", "", s)
    return s.strip()


def _dream_analysis_system_prompt() -> str:
    return (
        "你是熟悉意象、情绪与叙事的心理取向梦境工作助手（非临床诊断）。"
        "请用中文写作，语气温暖、具体，避免空泛套话；不要下精神疾病诊断或用药建议；"
        "若涉及创伤或强烈痛苦，用谨慎措辞并鼓励用户在现实中寻求专业支持。"
        "只输出一个 JSON 对象，不要 markdown，不要 JSON 以外的文字。键与要求如下：\n"
        "overview：string，约 180–320 字。复述梦境关键情节与氛围，并点出可能的内在张力或转折。\n"
        "symbols：array of string，4–7 条；每条 25–80 字，解释梦里具体意象/人物/场景可能象征什么（用「可能」「像是」等开放表述）。\n"
        "emotions：string，约 200–380 字。分层描述：梦里显性情绪、潜在或被压抑的感受、"
        "与常见现实压力源的「可能」关联（工作、关系、自我期待、失控感等），避免武断归因。\n"
        "suggestions：array of string，3–5 条；每条为可操作的自我关照或记录/反思提示（非医疗指令）。\n"
        "themes：array of string，4–8 个简短中文主题词（2–6 字）。\n"
        "mood：string，一句中文概括整体情绪色彩。\n"
        "snippet：string，从用户原文摘录 1–2 句，合计不超过 120 字。"
    )


def _chat_completion_request(
    api_url: str,
    api_key: str,
    messages: list,
    model: str,
    *,
    temperature: float = 0.35,
    max_tokens: int = 1024,
    json_object: bool = True,
    extra_headers: dict | None = None,
) -> str:
    body = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
        "max_tokens": max_tokens,
    }
    if json_object:
        body["response_format"] = {"type": "json_object"}
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
    }
    if extra_headers:
        headers.update(extra_headers)
    req = urllib.request.Request(
        api_url,
        data=json.dumps(body, ensure_ascii=False).encode("utf-8"),
        headers=headers,
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=120) as resp:
            raw = resp.read().decode("utf-8", errors="replace")
            data = json.loads(raw)
    except urllib.error.HTTPError as e:
        err_body = e.read().decode("utf-8", errors="replace")[:4000]
        logger.warning("LLM HTTPError %s: %s", e.code, err_body)
        try:
            err_json = json.loads(err_body)
            em = err_json.get("error")
            if isinstance(em, dict):
                msg = em.get("message") or str(em)
            else:
                msg = str(em) if em else err_body[:800]
        except (json.JSONDecodeError, TypeError):
            msg = err_body[:800] or f"HTTP {e.code}"
        raise ValueError(msg) from e
    except urllib.error.URLError as e:
        logger.warning("LLM URLError: %s", e)
        raise ValueError("无法连接模型服务，请稍后重试。") from e
    try:
        return data["choices"][0]["message"]["content"]
    except (KeyError, IndexError, TypeError) as e:
        logger.warning("LLM unexpected payload: %s", raw[:2000])
        raise ValueError("模型返回格式异常。") from e


def dream_analysis_via_llm(dream_text: str) -> dict:
    system = _dream_analysis_system_prompt()
    user_msg = "请阅读以下梦境记录并完成上述 JSON：\n\n" + dream_text
    messages = [
        {"role": "system", "content": system},
        {"role": "user", "content": user_msg},
    ]

    ds_key = (os.environ.get("DEEPSEEK_API_KEY") or "").strip()
    if ds_key:
        model = (os.environ.get("DEEPSEEK_MODEL") or DEEPSEEK_DEFAULT_MODEL).strip()
        content = _chat_completion_request(
            DEEPSEEK_URL,
            ds_key,
            messages,
            model,
            temperature=0.45,
            max_tokens=4096,
        )
        provider = "deepseek"
    else:
        or_key = (os.environ.get("OPENROUTER_API_KEY") or "").strip()
        if not or_key:
            raise ValueError("未配置 DEEPSEEK_API_KEY 或 OPENROUTER_API_KEY。")
        model = (os.environ.get("OPENROUTER_MODEL") or OPENROUTER_DEFAULT_MODEL).strip()
        extra: dict = {}
        rref = (os.environ.get("OPENROUTER_HTTP_REFERER") or "").strip()
        ttl = (os.environ.get("OPENROUTER_APP_NAME") or "Dream journal").strip()
        if rref:
            extra["HTTP-Referer"] = rref
        if ttl:
            extra["X-Title"] = ttl
        content = _chat_completion_request(
            OPENROUTER_URL,
            or_key,
            messages,
            model,
            temperature=0.45,
            max_tokens=3600,
            extra_headers=extra or None,
        )
        provider = "openrouter"

    try:
        obj = json.loads(_strip_llm_json_fence(content))
    except json.JSONDecodeError as e:
        logger.warning("LLM JSON parse failed: %s", content[:1500])
        raise ValueError("模型未返回有效 JSON。") from e
    overview = (obj.get("overview") or obj.get("summary") or "").strip()
    mood = (obj.get("mood") or "").strip()
    snippet = (obj.get("snippet") or "").strip()
    emotions = (obj.get("emotions") or "").strip()
    themes_raw = obj.get("themes")
    if isinstance(themes_raw, list):
        themes = [str(t).strip() for t in themes_raw if str(t).strip()][:10]
    else:
        themes = []
    symbols_raw = obj.get("symbols")
    if isinstance(symbols_raw, list):
        symbols = [str(t).strip() for t in symbols_raw if str(t).strip()][:10]
    else:
        symbols = []
    sug_raw = obj.get("suggestions") or obj.get("self_care")
    if isinstance(sug_raw, list):
        suggestions = [str(t).strip() for t in sug_raw if str(t).strip()][:8]
    else:
        suggestions = []
    if not overview:
        raise ValueError("模型返回缺少 overview。")
    if not themes:
        themes = ["（未列出主题）"]
    if not symbols:
        symbols = ["（未列出意象）"]
    if not emotions:
        emotions = "（未展开情绪分析）"
    if not suggestions:
        suggestions = ["醒来后可以慢慢喝一口水，轻轻记下最鲜明的一个画面。"]
    return {
        "overview": overview,
        "symbols": symbols,
        "emotions": emotions,
        "suggestions": suggestions,
        "themes": themes,
        "mood": mood or "（未说明）",
        "snippet": snippet or "（无摘录）",
        "model": model,
        "provider": provider,
    }


def email_local_part(email: str) -> str:
    return email.split("@", 1)[0] if email else ""


def migrate_schema(conn):
    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            email TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL,
            created_at TEXT NOT NULL,
            email_verified INTEGER NOT NULL DEFAULT 1,
            avatar_filename TEXT
        )
        """
    )

    ucols = {r[1] for r in conn.execute("PRAGMA table_info(users)")}
    if "username" in ucols and "email" not in ucols:
        conn.execute("ALTER TABLE users ADD COLUMN email TEXT")
        conn.execute(
            "ALTER TABLE users ADD COLUMN email_verified INTEGER NOT NULL DEFAULT 1"
        )
        conn.execute("ALTER TABLE users ADD COLUMN avatar_filename TEXT")
        for row in conn.execute("SELECT id, username FROM users").fetchall():
            safe = re.sub(r"[^a-zA-Z0-9._-]", "_", row["username"] or "user")
            email = f"{safe}.{row['id']}@migrated.local"
            conn.execute("UPDATE users SET email = ? WHERE id = ?", (email, row["id"]))
    else:
        if "email" not in ucols:
            conn.execute("ALTER TABLE users ADD COLUMN email TEXT")
        if "email_verified" not in ucols:
            conn.execute(
                "ALTER TABLE users ADD COLUMN email_verified INTEGER NOT NULL DEFAULT 1"
            )
        if "avatar_filename" not in ucols:
            conn.execute("ALTER TABLE users ADD COLUMN avatar_filename TEXT")
        if "username" in ucols:
            for row in conn.execute(
                "SELECT id, username, email FROM users WHERE email IS NULL OR email = ''"
            ).fetchall():
                safe = re.sub(r"[^a-zA-Z0-9._-]", "_", row["username"] or "user")
                email = f"{safe}.{row['id']}@migrated.local"
                conn.execute("UPDATE users SET email = ? WHERE id = ?", (email, row["id"]))

    ucols = {r[1] for r in conn.execute("PRAGMA table_info(users)")}
    if "nickname" not in ucols:
        conn.execute("ALTER TABLE users ADD COLUMN nickname TEXT")

    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS email_otps (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            email TEXT NOT NULL,
            purpose TEXT NOT NULL,
            code_hash TEXT NOT NULL,
            expires_at TEXT NOT NULL,
            created_at TEXT NOT NULL
        )
        """
    )
    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS password_resets (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            token TEXT UNIQUE NOT NULL,
            expires_at TEXT NOT NULL,
            used INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """
    )

    dcur = conn.execute(
        "SELECT name FROM sqlite_master WHERE type='table' AND name='dreams'"
    )
    if dcur.fetchone():
        dcols = {r[1] for r in conn.execute("PRAGMA table_info(dreams)")}
        if "user_id" not in dcols:
            conn.execute("ALTER TABLE dreams ADD COLUMN user_id INTEGER REFERENCES users(id)")
        if "dream_color" not in dcols:
            conn.execute(
                f"ALTER TABLE dreams ADD COLUMN dream_color TEXT NOT NULL DEFAULT '{DEFAULT_DREAM_COLOR}'"
            )
        if "dream_on" not in dcols:
            conn.execute("ALTER TABLE dreams ADD COLUMN dream_on TEXT NOT NULL DEFAULT ''")
            for row in conn.execute("SELECT id, created_at FROM dreams").fetchall():
                dday = local_date_str_from_iso(row["created_at"] or "")
                conn.execute(
                    "UPDATE dreams SET dream_on = ? WHERE id = ?",
                    (dday, row["id"]),
                )
    else:
        conn.execute(
            f"""
            CREATE TABLE dreams (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER REFERENCES users(id),
                content TEXT NOT NULL,
                created_at TEXT NOT NULL,
                dream_color TEXT NOT NULL DEFAULT '{DEFAULT_DREAM_COLOR}',
                dream_on TEXT NOT NULL DEFAULT ''
            )
            """
        )

    try:
        conn.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_users_email ON users(email)")
    except sqlite3.OperationalError:
        pass


def init_db():
    conn = get_db()
    migrate_schema(conn)
    conn.commit()
    conn.close()


def base_url():
    return (os.environ.get("BASE_URL") or request.url_root).rstrip("/")


def _send_email_via_resend(to_addr: str, subject: str, body: str) -> tuple[bool, str | None]:
    """https://resend.com/docs/api-reference/emails/send-email"""
    api_key = (os.environ.get("RESEND_API_KEY") or "").strip()
    if not api_key:
        return False, None
    from_email = (
        (os.environ.get("RESEND_FROM") or os.environ.get("SMTP_FROM") or "onboarding@resend.dev")
        .strip()
    )
    payload = {
        "from": from_email,
        "to": [to_addr],
        "subject": subject,
        "text": body,
    }
    req = urllib.request.Request(
        "https://api.resend.com/emails",
        data=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            raw = resp.read().decode("utf-8", errors="replace")
            if resp.status not in (200, 201):
                logger.warning("Resend 非成功状态 %s: %s", resp.status, raw[:2000])
                return False, f"Resend 返回 HTTP {resp.status}，请检查 RESEND_FROM 是否已在 Resend 控制台验证。"
            return True, None
    except urllib.error.HTTPError as e:
        err_body = e.read().decode("utf-8", errors="replace")[:4000]
        logger.warning("Resend HTTPError %s: %s", e.code, err_body)
        msg = err_body
        try:
            o = json.loads(err_body)
            if isinstance(o, dict) and o.get("message"):
                msg = str(o.get("message"))
        except (json.JSONDecodeError, TypeError):
            pass
        return False, (msg[:400] if msg else f"Resend HTTP {e.code}")
    except urllib.error.URLError as e:
        logger.warning("Resend URLError: %s", e)
        return False, "无法连接 Resend API，请检查网络或 API Key。"


def _send_email_via_smtp(to_addr: str, subject: str, body: str) -> tuple[bool, str | None]:
    host = os.environ.get("SMTP_HOST", "").strip()
    if not host:
        return False, None
    port = int(os.environ.get("SMTP_PORT", "587") or 587)
    user = os.environ.get("SMTP_USER", "").strip()
    password = os.environ.get("SMTP_PASSWORD", "")
    from_addr = os.environ.get("SMTP_FROM", user).strip() or user

    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = from_addr
    msg["To"] = to_addr
    msg.set_content(body)

    tls_env = os.environ.get("SMTP_USE_TLS", "1").strip().lower()
    use_starttls = tls_env not in ("0", "false", "no")
    ssl_env = os.environ.get("SMTP_SSL", "").strip().lower()
    use_implicit_ssl = ssl_env in ("1", "true", "yes") or port == 465

    try:
        if use_implicit_ssl:
            with smtplib.SMTP_SSL(host, port, timeout=30) as smtp:
                if user:
                    smtp.login(user, password)
                smtp.send_message(msg)
        else:
            with smtplib.SMTP(host, port, timeout=30) as smtp:
                if use_starttls:
                    smtp.starttls()
                if user:
                    smtp.login(user, password)
                smtp.send_message(msg)
        return True, None
    except smtplib.SMTPException as e:
        logger.exception("SMTP 发送失败: %s", e)
        return False, f"SMTP 错误：{e!s}"[:400]
    except OSError as e:
        logger.exception("发送邮件失败: %s", e)
        return False, f"网络或连接错误：{e!s}"[:400]


def send_email(to_addr: str, subject: str, body: str) -> tuple[bool, str | None]:
    """
    投递邮件。优先使用 RESEND_API_KEY；否则使用 SMTP。
    返回 (是否已尝试并成功投递, 失败时的简短说明)。
    """
    resend_key = (os.environ.get("RESEND_API_KEY") or "").strip()
    if resend_key:
        return _send_email_via_resend(to_addr, subject, body)

    host = os.environ.get("SMTP_HOST", "").strip()
    if host:
        return _send_email_via_smtp(to_addr, subject, body)

    logger.warning(
        "未配置 RESEND_API_KEY 或 SMTP_HOST，邮件未发送。收件人: %s\n-----\n%s\n-----",
        to_addr,
        body,
    )
    return False, "未配置发信：请设置环境变量 RESEND_API_KEY（推荐）或 SMTP_HOST 等。"


def issue_otp(conn, email: str, purpose: str) -> str:
    code = f"{secrets.randbelow(900000) + 100000:06d}"
    exp = (utc_now() + timedelta(minutes=OTP_TTL_MINUTES)).isoformat()
    conn.execute(
        "DELETE FROM email_otps WHERE email = ? AND purpose = ?",
        (email, purpose),
    )
    conn.execute(
        """
        INSERT INTO email_otps (email, purpose, code_hash, expires_at, created_at)
        VALUES (?, ?, ?, ?, ?)
        """,
        (email, purpose, generate_password_hash(code), exp, utc_now_iso()),
    )
    return code


def verify_otp(conn, email: str, purpose: str, code: str) -> bool:
    rows = conn.execute(
        """
        SELECT id, code_hash, expires_at FROM email_otps
        WHERE email = ? AND purpose = ?
        ORDER BY id DESC LIMIT 8
        """,
        (email, purpose),
    ).fetchall()
    now = utc_now()
    for r in rows:
        try:
            exp = datetime.fromisoformat(r["expires_at"].replace("Z", "+00:00"))
        except ValueError:
            continue
        if exp < now:
            continue
        if check_password_hash(r["code_hash"], code.strip()):
            conn.execute("DELETE FROM email_otps WHERE id = ?", (r["id"],))
            return True
    return False


def user_avatar_url(user_id: int, avatar_filename: str | None) -> str:
    if avatar_filename:
        base = url_for("static", filename=f"user_avatars/{user_id}/{avatar_filename}")
        return f"{base}?v={quote(avatar_filename, safe='')}"
    return url_for("static", filename="avatars/default.svg")


def insert_new_user(conn, email: str, password_hash: str, now_iso: str, nickname: str) -> int:
    nick = sanitize_nickname(nickname, email_local_part(email))
    cols = {r[1] for r in conn.execute("PRAGMA table_info(users)")}
    if "username" in cols:
        uname = re.sub(r"[^a-zA-Z0-9._-]", "_", email)
        if len(uname) > 80:
            uname = uname[:80]
        conn.execute(
            """
            INSERT INTO users (email, username, password_hash, created_at, email_verified, avatar_filename, nickname)
            VALUES (?, ?, ?, ?, 1, NULL, ?)
            """,
            (email, uname or "user", password_hash, now_iso, nick),
        )
    else:
        conn.execute(
            """
            INSERT INTO users (email, password_hash, created_at, email_verified, avatar_filename, nickname)
            VALUES (?, ?, ?, 1, NULL, ?)
            """,
            (email, password_hash, now_iso, nick),
        )
    row = conn.execute("SELECT id FROM users WHERE email = ?", (email,)).fetchone()
    return row["id"]


app = Flask(__name__)
app.config["SECRET_KEY"] = os.environ.get("SECRET_KEY", "dev-change-me-in-production")
app.config["MAX_CONTENT_LENGTH"] = 16 * 1024 * 1024


@app.template_filter("localtime")
def _filter_localtime(iso_s):
    return format_display_datetime(iso_s or "")


@app.context_processor
def inject_current_user():
    uid = session.get("user_id")
    if not uid:
        return {"current_user": None}
    conn = get_db()
    row = conn.execute(
        "SELECT id, email, avatar_filename, nickname FROM users WHERE id = ?", (uid,)
    ).fetchone()
    conn.close()
    if not row:
        session.pop("user_id", None)
        return {"current_user": None}
    nick = (row["nickname"] or "").strip()
    disp = nick or email_local_part(row["email"])
    return {
        "current_user": {
            "id": row["id"],
            "email": row["email"],
            "display": disp,
            "avatar_url": user_avatar_url(row["id"], row["avatar_filename"]),
        }
    }


@app.context_processor
def inject_nav_and_palette():
    ep = request.endpoint
    nav_active = None
    if ep == "index":
        nav_active = "home"
    elif ep in ("me", "dream_detail", "nickname"):
        nav_active = "me"
    elif ep == "login":
        nav_active = "login"
    elif ep in ("register", "register_confirm"):
        nav_active = "register"
    return {
        "nav_active": nav_active,
        "dream_color_palette": DREAM_COLOR_PALETTE,
    }


def login_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not session.get("user_id"):
            return redirect(url_for("login", next=request.path))
        return f(*args, **kwargs)

    return decorated


def current_user_id():
    return session.get("user_id")


def save_dream_from_request(user_id: int) -> bool:
    """若表单中有梦境正文则写入数据库，返回是否已插入。"""
    content = (request.form.get("content") or "").strip()
    if not content:
        return False
    color = dream_color_for_save(request.form.get("dream_color", ""))
    dream_on = parse_dream_on_field(request.form.get("dream_on", ""))
    if not dream_on:
        dream_on = datetime.now(_display_zoneinfo()).strftime("%Y-%m-%d")
    now = utc_now_iso()
    conn = get_db()
    conn.execute(
        """
        INSERT INTO dreams (user_id, content, created_at, dream_color, dream_on)
        VALUES (?, ?, ?, ?, ?)
        """,
        (user_id, content, now, color, dream_on),
    )
    conn.commit()
    conn.close()
    return True


def dream_calendar_entries(uid: int):
    conn = get_db()
    rows = conn.execute(
        """
        SELECT dream_on, dream_color, id, created_at
        FROM dreams WHERE user_id = ? ORDER BY dream_on, id
        """,
        (uid,),
    ).fetchall()
    conn.close()
    by_day = defaultdict(list)
    for r in rows:
        day = (r["dream_on"] or "").strip()
        if not day:
            day = local_date_str_from_iso(r["created_at"] or "")
        by_day[day].append(
            {
                "color": sanitize_hex_color(r["dream_color"]),
                "id": int(r["id"]),
            }
        )
    return [{"day": k, "entries": v} for k, v in sorted(by_day.items())]


@app.route("/", methods=["GET", "POST"])
def index():
    if request.method == "POST":
        if not session.get("user_id"):
            return redirect(url_for("login", next=request.path))
        uid = current_user_id()
        if save_dream_from_request(uid):
            flash("梦境已保存。", "ok")
        else:
            flash("请填写梦境内容后再保存。", "error")
        return redirect(url_for("index"))
    today_do = datetime.now(_display_zoneinfo()).strftime("%Y-%m-%d")
    return render_template("landing.html", today_dream_on=today_do)


@app.route("/register", methods=["GET", "POST"])
def register():
    if current_user_id():
        return redirect(url_for("index"))
    err = None
    if request.method == "POST":
        email = normalize_email(request.form.get("email", ""))
        if not is_valid_email(email):
            err = "请输入有效的邮箱地址。"
        else:
            conn = get_db()
            exists = conn.execute(
                "SELECT 1 FROM users WHERE email = ?", (email,)
            ).fetchone()
            if exists:
                conn.close()
                err = "该邮箱已注册，请直接登录或找回密码。"
            else:
                code = issue_otp(conn, email, "register")
                conn.commit()
                conn.close()
                sent, send_err = send_email(
                    email,
                    "梦境记录 — 注册验证码",
                    f"你的注册验证码是：{code}\n{OTP_TTL_MINUTES} 分钟内有效。\n如非本人操作请忽略。",
                )
                session["register_email"] = email
                if not sent:
                    flash(
                        "验证码未能发送到你的邮箱。"
                        + (f" {send_err}" if send_err else "")
                        + " 请在服务器环境变量中配置 RESEND_API_KEY（推荐）或 SMTP_HOST 等发信参数。"
                        + " 开发调试时，可在运行本程序的终端日志里搜索「你的注册验证码是」。",
                        "error",
                    )
                return redirect(url_for("register_confirm"))
    return render_template("register.html", error=err)


@app.route("/register/confirm", methods=["GET", "POST"])
def register_confirm():
    if current_user_id():
        return redirect(url_for("index"))
    email = session.get("register_email")
    if not email:
        return redirect(url_for("register"))
    err = None
    if request.method == "POST":
        code = (request.form.get("code") or "").strip()
        password = request.form.get("password") or ""
        if len(code) < 4:
            err = "请输入邮箱收到的验证码。"
        elif len(password) < 6:
            err = "密码至少 6 位。"
        else:
            conn = get_db()
            if conn.execute("SELECT 1 FROM users WHERE email = ?", (email,)).fetchone():
                conn.close()
                session.pop("register_email", None)
                err = "该邮箱已注册，请直接登录。"
            elif not verify_otp(conn, email, "register", code):
                conn.close()
                err = "验证码错误或已过期，请点击「重新发送验证码」。"
            else:
                now = utc_now_iso()
                h = generate_password_hash(password)
                nick_in = (request.form.get("nickname") or "").strip()
                uid = insert_new_user(conn, email, h, now, nick_in)
                conn.commit()
                conn.close()
                session.pop("register_email", None)
                session["user_id"] = uid
                return redirect(url_for("index"))
    return render_template("register_confirm.html", email=email, error=err)


@app.route("/register/resend", methods=["POST"])
def register_resend():
    if current_user_id():
        return redirect(url_for("index"))
    email = session.get("register_email")
    if not email:
        return redirect(url_for("register"))
    conn = get_db()
    if conn.execute("SELECT 1 FROM users WHERE email = ?", (email,)).fetchone():
        conn.close()
        return redirect(url_for("login"))
    code = issue_otp(conn, email, "register")
    conn.commit()
    conn.close()
    sent, send_err = send_email(
        email,
        "梦境记录 — 注册验证码",
        f"你的注册验证码是：{code}\n{OTP_TTL_MINUTES} 分钟内有效。",
    )
    if not sent:
        flash(
            "重新发送失败，邮件仍未发出。"
            + (f" {send_err}" if send_err else "")
            + " 请检查 RESEND_API_KEY 或 SMTP 配置；开发时可在终端日志查看验证码。",
            "error",
        )
    return redirect(url_for("register_confirm"))


@app.route("/login", methods=["GET", "POST"])
def login():
    if current_user_id():
        return redirect(url_for("index"))
    err = None
    if request.method == "POST":
        email = normalize_email(request.form.get("email", ""))
        password = request.form.get("password") or ""
        conn = get_db()
        row = conn.execute(
            "SELECT id, password_hash FROM users WHERE email = ?", (email,)
        ).fetchone()
        conn.close()
        if row and check_password_hash(row["password_hash"], password):
            session["user_id"] = row["id"]
            nxt = request.form.get("next") or request.args.get("next") or url_for("index")
            if isinstance(nxt, str) and nxt.startswith("/"):
                return redirect(nxt)
            return redirect(url_for("index"))
        err = "邮箱或密码错误。"
    return render_template("login.html", error=err)


@app.route("/forgot-password", methods=["GET", "POST"])
def forgot_password():
    if current_user_id():
        return redirect(url_for("index"))
    err = None
    ok = None
    if request.method == "POST":
        email = normalize_email(request.form.get("email", ""))
        if not is_valid_email(email):
            err = "请输入有效邮箱。"
        else:
            conn = get_db()
            row = conn.execute("SELECT id FROM users WHERE email = ?", (email,)).fetchone()
            if row:
                token = secrets.token_urlsafe(32)
                exp = (utc_now() + timedelta(hours=RESET_TOKEN_TTL_HOURS)).isoformat()
                conn.execute(
                    """
                    INSERT INTO password_resets (user_id, token, expires_at, used, created_at)
                    VALUES (?, ?, ?, 0, ?)
                    """,
                    (row["id"], token, exp, utc_now_iso()),
                )
                conn.commit()
                link = f"{base_url()}{url_for('reset_password', token=token)}"
                sent, send_err = send_email(
                    email,
                    "梦境记录 — 重置密码",
                    f"请点击以下链接重置密码（{RESET_TOKEN_TTL_HOURS} 小时内有效）：\n{link}\n如非本人操作请忽略。",
                )
                if not sent:
                    flash(
                        (send_err or "未能发送重置邮件。")
                        + " 请配置 RESEND_API_KEY 或 SMTP；开发时可在终端日志中查找重置链接。",
                        "error",
                    )
            conn.close()
            ok = "若该邮箱已注册，你将收到一封含重置链接的邮件（需已正确配置 Resend 或 SMTP）。未收到时请检查垃圾箱或发信配置。"
    return render_template("forgot_password.html", error=err, ok=ok)


@app.route("/reset-password/<token>", methods=["GET", "POST"])
def reset_password(token):
    if current_user_id():
        return redirect(url_for("index"))
    err = None
    conn = get_db()
    row = conn.execute(
        """
        SELECT id, user_id, expires_at, used FROM password_resets
        WHERE token = ? ORDER BY id DESC LIMIT 1
        """,
        (token,),
    ).fetchone()
    if not row or row["used"]:
        conn.close()
        return render_template("reset_invalid.html"), 400
    try:
        exp = datetime.fromisoformat(row["expires_at"].replace("Z", "+00:00"))
    except ValueError:
        conn.close()
        return render_template("reset_invalid.html"), 400
    if exp < utc_now():
        conn.close()
        return render_template("reset_invalid.html"), 400

    if request.method == "POST":
        p1 = request.form.get("password") or ""
        p2 = request.form.get("password2") or ""
        if len(p1) < 6:
            err = "密码至少 6 位。"
        elif p1 != p2:
            err = "两次输入的密码不一致。"
        else:
            h = generate_password_hash(p1)
            conn.execute(
                "UPDATE users SET password_hash = ? WHERE id = ?",
                (h, row["user_id"]),
            )
            conn.execute(
                "UPDATE password_resets SET used = 1 WHERE id = ?", (row["id"],)
            )
            conn.commit()
            conn.close()
            return redirect(url_for("login"))
        conn.close()
        return render_template("reset_password.html", token=token, error=err)
    conn.close()
    return render_template("reset_password.html", token=token, error=err)


@app.route("/logout", methods=["POST"])
def logout():
    session.pop("user_id", None)
    return redirect(url_for("index"))


@app.route("/me", methods=["GET"])
@login_required
def me():
    uid = current_user_id()

    conn = get_db()
    rows = conn.execute(
        """
        SELECT id, content, created_at, dream_color, dream_on FROM dreams
        WHERE user_id = ? ORDER BY id DESC
        """,
        (uid,),
    ).fetchall()
    dreams = []
    for r in rows:
        d = dict(r)
        d["dream_color"] = sanitize_hex_color(d.get("dream_color") or "")
        dreams.append(d)
    u = conn.execute(
        "SELECT email, avatar_filename, nickname FROM users WHERE id = ?", (uid,)
    ).fetchone()
    conn.close()
    avatar_large = user_avatar_url(uid, u["avatar_filename"])
    cal = dream_calendar_entries(uid)
    today_cal = datetime.now(_display_zoneinfo()).strftime("%Y-%m-%d")
    tz_name = (os.environ.get("APP_TIMEZONE") or "Asia/Shanghai").strip()
    return render_template(
        "me.html",
        dreams=dreams,
        avatar_large=avatar_large,
        calendar_by_day=cal,
        calendar_today=today_cal,
        display_tz_name=tz_name,
    )


@app.route("/me/avatar", methods=["POST"])
@login_required
def upload_avatar():
    uid = current_user_id()
    if "file" not in request.files:
        flash("请选择一张图片。", "error")
        return redirect(url_for("me"))
    f = request.files["file"]
    if not f or not f.filename:
        flash("未收到上传文件。", "error")
        return redirect(url_for("me"))
    ext = Path(secure_filename(f.filename)).suffix.lower()
    if ext not in ALLOWED_AVATAR_EXT:
        flash("头像仅支持 jpg、png、gif、webp。", "error")
        return redirect(url_for("me"))
    save_name = f"{uuid.uuid4().hex}{ext}"
    user_dir = AVATAR_ROOT / str(uid)
    user_dir.mkdir(parents=True, exist_ok=True)
    f.save(user_dir / save_name)
    conn = get_db()
    conn.execute(
        "UPDATE users SET avatar_filename = ? WHERE id = ?",
        (save_name, uid),
    )
    conn.commit()
    conn.close()
    flash("头像已更新。", "ok")
    return redirect(url_for("me"))


@app.route("/me/nickname", methods=["GET", "POST"])
@login_required
def nickname():
    uid = current_user_id()
    if request.method == "GET":
        conn = get_db()
        row = conn.execute(
            "SELECT email, nickname FROM users WHERE id = ?", (uid,)
        ).fetchone()
        conn.close()
        if not row:
            flash("用户不存在。", "error")
            return redirect(url_for("me"))
        current_nick = (row["nickname"] or "").strip()
        return render_template(
            "nickname_edit.html",
            email=row["email"],
            current_nick=current_nick,
        )
    conn = get_db()
    row = conn.execute("SELECT email FROM users WHERE id = ?", (uid,)).fetchone()
    if not row:
        conn.close()
        flash("用户不存在。", "error")
        return redirect(url_for("me"))
    fb = email_local_part(row["email"])
    nick = sanitize_nickname(request.form.get("nickname", ""), fb)
    conn.execute("UPDATE users SET nickname = ? WHERE id = ?", (nick, uid))
    conn.commit()
    conn.close()
    flash("昵称已保存。", "ok")
    return redirect(url_for("me"))


@app.route("/dream/<int:dream_id>")
@login_required
def dream_detail(dream_id):
    uid = current_user_id()
    conn = get_db()
    row = conn.execute(
        """
        SELECT id, content, created_at, dream_color, dream_on FROM dreams
        WHERE id = ? AND user_id = ?
        """,
        (dream_id, uid),
    ).fetchone()
    conn.close()
    if not row:
        return redirect(url_for("me"))
    dream = dict(row)
    dream["dream_color"] = sanitize_hex_color(dream.get("dream_color") or "")
    don = (dream.get("dream_on") or "").strip()
    dream["dream_on"] = don or local_date_str_from_iso(dream.get("created_at") or "")
    return render_template("dream_detail.html", dream=dream)


@app.route("/me/analyze", methods=["POST"])
@login_required
def analyze_dream():
    uid = current_user_id()
    data = request.get_json(silent=True) or {}
    dream_id = data.get("dream_id")
    if dream_id is None:
        return jsonify({"error": "缺少 dream_id"}), 400
    try:
        dream_id = int(dream_id)
    except (TypeError, ValueError):
        return jsonify({"error": "dream_id 无效"}), 400

    conn = get_db()
    row = conn.execute(
        "SELECT id, content FROM dreams WHERE id = ? AND user_id = ?",
        (dream_id, uid),
    ).fetchone()
    conn.close()
    if not row:
        return jsonify({"error": "记录不存在"}), 404

    full = row["content"] or ""
    text = full[:MAX_DREAM_CHARS_FOR_ANALYSIS]
    if len(full) > MAX_DREAM_CHARS_FOR_ANALYSIS:
        text = text + "\n\n（后文已截断，仅分析前若干字。）"

    try:
        result = dream_analysis_via_llm(text)
    except ValueError as e:
        msg = str(e)
        if "未配置 DEEPSEEK_API_KEY 或 OPENROUTER_API_KEY" in msg:
            return jsonify(
                {"error": "未配置 AI：请在环境变量或 .env 中设置 DEEPSEEK_API_KEY（优先）或 OPENROUTER_API_KEY。"}
            ), 503
        return jsonify({"error": msg}), 502
    except Exception:
        logger.exception("dream analyze failed dream_id=%s", dream_id)
        return jsonify({"error": "分析失败，请稍后重试。"}), 502

    return jsonify(
        {
            "dream_id": dream_id,
            "overview": result["overview"],
            "symbols": result["symbols"],
            "emotions": result["emotions"],
            "suggestions": result["suggestions"],
            "summary": result["overview"],
            "themes": result["themes"],
            "mood": result["mood"],
            "snippet": result["snippet"],
            "provider": result.get("provider"),
            "model": result.get("model"),
        }
    )


# 兼容旧前端路径：重定向到新接口逻辑由前端更新为主；保留别名避免书签失效
@app.route("/me/analyze_fake", methods=["POST"])
@login_required
def analyze_fake():
    return analyze_dream()


@app.route("/me/upload_voice", methods=["POST"])
@login_required
def upload_voice():
    uid = current_user_id()
    if "file" not in request.files:
        return jsonify({"error": "没有文件字段 file"}), 400
    f = request.files["file"]
    if not f or not f.filename:
        return jsonify({"error": "未选择文件"}), 400

    raw_name = secure_filename(f.filename) or "recording"
    ext = Path(raw_name).suffix.lower()
    if ext not in ALLOWED_AUDIO_EXT:
        ext = ".webm"
    save_name = f"{uuid.uuid4().hex}{ext}"
    user_dir = UPLOAD_ROOT / str(uid)
    user_dir.mkdir(parents=True, exist_ok=True)
    path = user_dir / save_name
    f.save(path)

    rel_url = f"/static/user_audio/{uid}/{save_name}"
    return jsonify(
        {
            "ok": True,
            "url": rel_url,
            "filename": save_name,
            "message": "已保存到服务器。",
        }
    )


if __name__ == "__main__":
    init_db()
    app.run(host="127.0.0.1", port=5000, debug=True)
