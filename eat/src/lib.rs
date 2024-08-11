use std::cell::RefCell;
use std::cmp;
use std::collections::TryReserveError;
use std::error;
use std::fmt;
use std::io::Read;
use std::rc::Rc;

// TODO: Delete
pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

/// Opening brace, the JSON separator that denotes the start an object value.
pub static SEP_BRACE_O: char = '{';

/// Closing brace, the JSON separator that denotes the end of an object value.
pub static SEP_BRACE_C: char = '}';

/// Opening bracket, the JSON separator that denotes the start of an array value.
pub static SEP_BRACK_O: char = '[';

/// Closing bracket, the JSON separator that denotes the end of an array value.
pub static SEP_BRACK_C: char = ']';

/// Comma, the JSON separator that appears between the members of objects and arrays.
pub static SEP_COMMA: char = ',';

/// Colon, the JSON separator that appears between the key and value parts of an object member.
pub static SEP_COLON: char = ':';

/// JSON keyword `false`.
pub static KEY_FALSE: &str = "false";

/// JSON keyword `true`.
pub static KEY_TRUE: &str = "true";

/// JSON keyword `null`.
pub static KEY_NULL: &str = "null";

/// Position of token or error within a JSON input stream. This position is relative to the start of
/// the [Stream], not the [Buf].
#[derive(Debug, Default, Clone, Copy)]
pub struct Pos {
    pub byte_off: u64,
    pub char_off: u64,
    pub line: u64,
    pub col: u64,
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "line {}, column {}, byte {}",
            self.line, self.col, self.byte_off,
        )
    }
}

/// Category of JSON error.
#[derive(Debug, Clone, Copy)]
pub enum ErrorCat {
    /// Read error in underlying stream.
    Read,
    /// Lexical error in JSON.
    Lex,
}

/// Represents either an error reading the underlying stream
/// ([ErrorCat::Read]) or a lexical error when tokenizing the JSON
/// ([ErrorCat::Lex]).
#[derive(Debug, Clone)]
pub struct Error {
    pub cat: ErrorCat,
    pub desc: String,
    pub pos: Pos,
    source: Option<Rc<dyn error::Error + 'static>>,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = match self.cat {
            ErrorCat::Read => "read",
            ErrorCat::Lex => "lexical",
        };
        write!(f, "{} error: {} at {}", prefix, self.desc, self.pos)?;
        if let Some(source) = self.source.as_ref() {
            write!(f, ": caused by {}", source)?;
        }
        Ok(())
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        self.source.as_ref().map(|rc| rc.as_ref())
    }
}

/// A JSON token read from a [Buf].
#[derive(Debug)]
pub enum Tok<'a> {
    /// Separator token.
    ///
    /// Contains the separator literally as it appears in the JSON input. May have one of six
    /// possible values:
    /// - [SEP_BRACE_O]
    /// - [SEP_BRACE_C]
    /// - [SEP_BRACK_O]
    /// - [SEP_BRACK_C]
    /// - [SEP_COMMA]
    /// - [SEP_COLON]
    Sep(char),

    /// Number token.
    ///
    /// Contains the number value literally as it appears in the JSON input.
    Num(&'a str),

    /// String token.
    ///
    /// Contains the string value literally as it appears in the JSON input, including the opening
    /// and closing double quotation mark (`"`).
    ///
    /// Examples: `""`, `"foo"`
    Str(&'a str),

    /// Keyword token.
    ///
    /// Contains the keyword literally as it appears in the JSON input. May have one of three
    /// possible values:
    /// - [KEY_FALSE]
    /// - [KEY_TRUE]
    /// - [KEY_NULL]
    Key(&'static str),

    /// Whitespace token.
    ///
    /// Contains a JSON whitespace token literally as it appears in the JSON input.
    White(&'a str),

    /// End of usable input tokens.
    ///
    /// After all usable input has been consumed in the buffer, there may still be more unusable
    /// input in the form of a partial token. This unusable remainder, if any, is included with the
    /// token.
    End(&'a str),

    /// Error token.
    ///
    /// Indicates that a lexical or syntactic error was detected. Includes the error details,
    /// including its position within the buffer.
    Err(Error),
}

/// Default value for the initial capacity of a [Buf], in bytes. This
/// value will be used as the starting buffer size in a [Stream] unless
/// overridden with [StreamBuilder::init_buf_len].
const DEFAULT_INIT_BUF_LEN: usize = 4 * 1024;

/// Default value for the maximum capacity of a [Buf], in bytes. This
/// will be used as the maximum possible buffer size in a [Stream]
/// unless overridden with [StreamBuilder::max_buf_len].
const DEFAULT_MAX_BUF_LEN: usize = 8 * 1024 * 1024;

/// Maximum possible value for the maximum capacity of a [Buf], in
/// bytes.
const MAX_MAX_BUF_LEN: usize = isize::MAX as usize;

pub struct Stream<R>
where
    R: Read,
{
    reader: R,
    shared: Rc<SharedBuf>,
    max_buf_len: usize,
}

impl<R> Stream<R>
where
    R: Read,
{
    /// Returns a new builder that can be used to build a stream.
    pub fn builder() -> StreamBuilder<R> {
        StreamBuilder {
            reader: None,
            init_buf_len: DEFAULT_INIT_BUF_LEN,
            max_buf_len: DEFAULT_MAX_BUF_LEN,
        }
    }

    /// Prepares the next buffer to be returned by [Self::buf].
    ///
    /// ### Returns
    ///
    /// Returns `true` if the next buffer is ready or `false` if the
    /// stream is now exhausted. If the return value is `true`, the
    /// buffer may be fetched by calling [Self::buf].
    ///
    /// ### Panics
    ///
    /// This function will panic if the buffer returned from the most
    /// recent previous call to [Self::buf]:
    /// 1. Has not been dropped.
    /// 2. Was not fully consumed.
    ///
    /// ### Errors
    ///
    /// This function does not return an error.
    ///
    /// Any errors encountered reading from the underlying reader will be
    /// reported as the first token from the [Buf] returned by [Self::buf].
    pub fn next(&mut self) -> bool {
        // Validate that previous buffer has been fully consumed and returned.
        let shared =
            Rc::get_mut(&mut self.shared).expect("Buf in use: drop current Buf before next()");
        let data = &mut shared.data;
        let mut meta = shared.meta.borrow_mut();
        if meta.is_consumed {
            panic!("Buf not fully consumed: read it up to End or Err")
        }
        // If the buffer has length 0, this stream is now exhausted.
        if data.is_empty() {
            return false;
        }
        // If the error or EOF has already been consumed from the buffer, this
        // stream is now exhausted. Discard the shared buffer and return false.
        if meta.is_eof || meta.err.is_some() {
            data.clear();
            return false;
        }
        // Read more input.
        Stream::<R>::read(&mut self.reader, data, &mut *meta, self.max_buf_len);
        // Indicate that there is more input to consume.
        true
    }

    /// Returns the buffer prepared by [Self::next].
    ///
    /// ### Returns
    ///
    /// Returns a [Buf] containing JSON tokens.
    ///
    /// ### Panics
    ///
    /// This function will panic unless it is called after a call to [Self::next] that returned
    /// `true`.
    ///
    /// There can be at most one call to this function per call to [Self::next], so if [Self::next]
    /// returned `true` but this function has already been called once, a subsequent call will
    /// panic until [Self::next] is called again returning `true`.
    ///
    /// ### Errors
    ///
    /// This function does not return an error.
    pub fn buf(&mut self) -> Buf {
        // Validate that this method call occurs after a call to next() that
        // returned true, i.e. that there is a buffer available.
        if Rc::strong_count(&self.shared) > 1 {
            panic!("Buf in use: drop current Buf before buf()")
        } else if self.shared.data.is_empty() {
            panic!("next() was not called, or returned false")
        }
        // Return buffer.
        let meta = self.shared.meta.borrow();
        assert!(meta.byte_off == 0);
        Buf {
            shared: Rc::clone(&self.shared),
            data_ref: &self.shared.data,
            meta_copy: meta.clone(),
            tok: Tok::Sep(SEP_BRACE_C),
        }
    }

    // Moves unconsumed bytes to the front of the data buffer and tries to resize it as necessary.
    fn shift(data: &mut Vec<u8>, meta: &mut MetaBuf, max_buf_len: usize) -> Result<usize, Error> {
        // Count the unconsumed remainder bytes.
        let rem = data.len() - meta.byte_off;
        // Move any unconsumed data to the front.
        data.copy_within(meta.byte_off.., 0);
        // Expand the buffer if we are not making enough progress.
        if (meta.byte_off as f32) / (data.len() as f32) < 0.5 {
            // Calculate the desired new capacity.
            let new_capacity = match data.len().checked_mul(2) {
                Some(double_len) => cmp::min(cmp::max(double_len, data.capacity()), max_buf_len),
                None => max_buf_len,
            };
            if data.capacity() < new_capacity {
                // Expand the buffer. If it fails, return error message that prevented the buffer
                // being expanded.
                data.try_reserve(new_capacity)
                    .map_err(|e: TryReserveError| Error {
                        cat: ErrorCat::Read,
                        desc: String::from("failed to expand buffer"),
                        pos: meta.pos,
                        source: Some(Rc::from(e)),
                    })?;
            } else if meta.byte_off == 0 {
                // If the buffer is already at maximum capacity AND we failed to make ANY progress,
                // this means there is a JSON string or number token that is larger than the buffer.
                // Since the only thing we could possibly do is allocate a bigger buffer that would
                // allow the whole token to be seen at once, and we can't do that, we return with an
                // error.
                let desc = format!(
                    "can't make progress with maxxed buffer of {} bytes (likely due to an offensively long string or number token)",
                    data.capacity()
                );
                return Err(Error {
                    cat: ErrorCat::Read,
                    desc: desc,
                    pos: meta.pos,
                    source: None,
                });
            }
        }
        // Update consumed byte offset to zero.
        meta.byte_off = 0;
        // Shift is successful.
        Ok(rem)
    }

    fn read(reader: &mut R, data: &mut Vec<u8>, meta: &mut MetaBuf, max_buf_len: usize) {
        // Move unconsumed bytes to the left and, if necessary, enlarge buffer.
        let rem = match Stream::<R>::shift(data, meta, max_buf_len) {
            Ok(rem) => rem,
            Err(e) => {
                meta.err = Some(e);
                return;
            }
        };
        // Read up to buffer capacity.
        let capacity = data.capacity();
        unsafe { data.set_len(capacity) }
        match reader.read(&mut data[rem..capacity - rem]) {
            Ok(num_read) => {
                unsafe {
                    data.set_len(rem + num_read);
                }
                meta.is_eof = num_read == 0;
            }
            Err(e) => {
                meta.err = Some(Error {
                    cat: ErrorCat::Read,
                    desc: String::from("failed to read"),
                    pos: meta.pos,
                    source: Some(Rc::from(e)),
                });
            }
        }
    }
}

pub struct StreamBuilder<R>
where
    R: Read,
{
    reader: Option<R>,
    init_buf_len: usize,
    max_buf_len: usize,
}

impl<R> StreamBuilder<R>
where
    R: Read,
{
    pub fn reader(mut self, reader: R) -> Self {
        self.reader = Some(reader);
        self
    }

    pub fn init_buf_len(mut self, init_buf_len: usize) -> Self {
        if init_buf_len < 1 {
            panic!("init_buf_len must be positive");
        } else if init_buf_len > self.max_buf_len {
            panic!(
                "init_buf_len must not exceed max_buf_len, but {} > {}",
                init_buf_len, self.max_buf_len,
            );
        }
        self.init_buf_len = init_buf_len;
        self
    }

    pub fn max_buf_len(mut self, max_buf_len: usize) -> Self {
        if max_buf_len < self.init_buf_len {
            panic!(
                "max_buf_len must not be less than init_buf_len, but {} < {}",
                max_buf_len, self.init_buf_len
            );
        } else if max_buf_len > MAX_MAX_BUF_LEN {
            panic!(
                "max_buf_len must not exceed MAX_MAX_BUF_LEN, but {} > {}",
                max_buf_len, MAX_MAX_BUF_LEN
            );
        }
        self.max_buf_len = max_buf_len;
        self
    }

    pub fn build(self) -> Stream<R> {
        Stream {
            reader: self.reader.expect("reader not provided"),
            shared: Rc::new(SharedBuf::alloc(self.init_buf_len)),
            max_buf_len: self.max_buf_len,
        }
    }
}

#[derive(Debug, Clone)]
struct MetaBuf {
    // Whether all usable JSON tokens have been consumed from the buffer. Once all the legitimate
    // JSON tokens have been consumed, there may still be an unused remainder that will have to be
    // moved to the front of the buffer.
    is_consumed: bool,

    // Whether the end of file has been seen in the input stream, meaning that this buffer now has
    // all possible remaining input on the stream.
    is_eof: bool,

    // Byte offset into the buffer that has been consumed so far.
    byte_off: usize,

    // Read position within the overall input stream. The Stream will refresh its own position from
    // this value when its next method is called.
    pos: Pos,

    // Fatal error to be transferred between Stream and Buf. This allows the Stream to push a read
    // error down to the Buf and Buf to push a lexical error up to the Stream.
    err: Option<Error>,
}

struct SharedBuf {
    // Memory for the buffer.
    data: Vec<u8>,

    // Metadata about the buffer.
    meta: RefCell<MetaBuf>,
}

impl SharedBuf {
    fn alloc(capacity: usize) -> SharedBuf {
        SharedBuf {
            data: Vec::with_capacity(capacity),
            meta: RefCell::new(MetaBuf {
                is_consumed: false,
                is_eof: false,
                byte_off: 0,
                pos: Pos::default(),
                err: None,
            }),
        }
    }
}

pub struct Buf<'a> {
    shared: Rc<SharedBuf>,
    data_ref: &'a Vec<u8>,
    meta_copy: MetaBuf,
    tok: Tok<'a>,
}

impl<'a> Buf<'a> {
    fn next(&mut self) -> bool {
        if self.meta_copy.is_consumed {
            false
        } else {
            let i = self.meta_copy.byte_off;
            let n = self.data_ref.len();
            if i == n {
                self.tok = Tok::End("");
                self.meta_copy.is_consumed = true;
            } else if self.meta_copy.err.is_some() {
                self.err(self.meta_copy.err.as_ref().unwrap().clone());
            } else {
                let byte_off = self.meta_copy.pos.byte_off;
                let x = self.data_ref[i];
                match x {
                    // Separators.
                    b'{' => self.sep('{'),
                    b'}' => self.sep('}'),
                    b'[' => self.sep('['),
                    b']' => self.sep(']'),
                    b',' => self.sep(','),
                    b':' => self.sep(':'),
                    // String literals.
                    b'"' => self.str(),
                    // Number literals.
                    b'-' => self.num_signed(),
                    b'0' => self.num_zero(),
                    b'1'..=b'9' => self.num_integer(1),
                    // Keywords.
                    b'f' => self.key(b"false"),
                    b't' => self.key(b"true"),
                    b'n' => self.key(b"null"),
                    // Whitespace.
                    b'\t' | b'\n' | b'\r' | b' ' => self.white(),
                    // Error.
                    _ => self.err_lex(format!("unexpected {}", describe_octet(x))),
                }
                self.meta_copy.byte_off += (self.meta_copy.pos.byte_off - byte_off) as usize;
            }
            true
        }
    }

    fn tok(&self) -> &'a Tok {
        &self.tok
    }

    fn pos(&self) -> Pos {
        self.meta_copy.pos
    }

    fn sep(&mut self, sep: char) {
        self.tok = Tok::Sep(sep);
        Buf::advance_bytes(&mut self.meta_copy.pos, 1);
    }

    fn str(&mut self) {
        let mut i = self.meta_copy.byte_off + 1;
        let n = self.data_ref.len();
        loop {
            if i == n && !self.meta_copy.is_eof {
                self.end();
            } else if i == n {
                self.err_lex(String::from("expected string character, got EOF"));
            } else {
                let x = self.data_ref[i];
                match x {
                    b'"' => {
                        self.tok = Tok::Num(self.slice_unchecked(self.meta_copy.byte_off, i + 1));
                        Buf::advance_bytes(
                            &mut self.meta_copy.pos,
                            i + 1 - self.meta_copy.byte_off,
                        );
                        return;
                    }
                    b'\\' => {
                        if self.str_escape(&mut i) {
                            return;
                        }
                    }
                    0..b' ' => {
                        self.err_lex(format!("{} not allowed in string", describe_octet(x)));
                        return;
                    }
                    b' '..b'"' | b'#'..b'\\' | b']'..=0x7f => i = i + 1,
                    0x80..0xc2 | 0xf5..=0xff => {
                        self.err_lex(format!(
                            "{} not allowed as first byte of a UTF-8 character",
                            describe_octet(8)
                        ));
                        return;
                    }
                    0xc2..0xe0 => {
                        if !self.str_multibyte(&mut i, 1) {
                            return;
                        }
                    }
                    0xe0..0xf0 => {
                        if !self.str_multibyte(&mut i, 2) {
                            return;
                        }
                    }
                    0xf0..0xf5 => {
                        if !self.str_multibyte(&mut i, 3) {
                            return;
                        }
                    }
                }
            }
        }
    }

    fn str_escape(&mut self, i: &mut usize) -> bool {
        *i += 1;
        let n = self.data_ref.len();
        // Determine type of escape sequence.
        if *i == n && !self.meta_copy.is_eof {
            self.end();
            return false;
        } else if *i == n {
            self.err_lex(String::from(
                "unfinished escape sequence in string, got EOF",
            ));
            return false;
        } else {
            let x = self.data_ref[*i];
            match x {
                b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => {
                    *i += 1;
                    return true;
                }
                b'u' => (),
                _ => {
                    self.err_lex(format!(
                        "invalid {} in string escape sequence after '\\'",
                        describe_octet(x)
                    ));
                    return false;
                }
            }
        }
        // Handle unicode escape sequence.
        for j in 0..4 {
            *i += 1;
            if *i == n && !self.meta_copy.is_eof {
                self.end();
                return false;
            } else if *i == n {
                self.err_lex(String::from(
                    "unfinished \\u unicode escape sequence in string, got EOF",
                ));
                return false;
            } else {
                let x = self.data_ref[*i];
                match x {
                    b'0'..=b'9' | b'A'..=b'F' | b'a'..=b'f' => (),
                    _ => {
                        self.err_lex(format!(
                            "invalid {} in string \\u unicode escape sequence",
                            describe_octet(x)
                        ));
                        return false;
                    }
                }
            }
        }
        return true;
    }

    fn str_multibyte(&mut self, i: &mut usize, rem: usize) -> bool {
        let n = self.data_ref.len();
        for j in 0..rem {
            *i += 1;
            if *i == n && !self.meta_copy.is_eof {
                self.end();
                return false;
            } else if *i == n {
                self.err_lex(format!(
                    "unfinished {}-byte UTF-8 sequence, got EOF after byte #{}",
                    rem + 1,
                    j + 1
                ));
                return false;
            } else {
                let x = self.data_ref[*i];
                match x {
                    0x80..0xc0 => (),
                    _ => {
                        self.err_lex(format!(
                            "invalid {} in {}-byte UTF-8 sequence byte #{}",
                            describe_octet(x),
                            rem + 1,
                            j + 1
                        ));
                        return false;
                    }
                }
            }
        }
        return true;
    }

    fn num_zero(&mut self) {
        let i = self.meta_copy.byte_off + 1;
        let n = self.data_ref.len();
        if i < n {
            // Zero encountered before end of buffer. Peek the next character to decide if there's a
            // valid token or an error.
            let x = self.data_ref[i];
            match x {
                b'\t' | b'\n' | b'\r' | b' ' | b'{' | b'}' | b'[' | b']' | b',' | b':' | b'"' => (),
                _ => {
                    self.err_lex(format!(
                        "unexpected {} in number after '0'",
                        describe_octet(x)
                    ));
                    return;
                }
            }
        } else if !self.meta_copy.is_eof {
            // Zero encountered at end of buffer. Need to see more input to decide if there's a
            // valid token or an error.
            self.end();
            return;
        }
        // At this point, we know we have a valid zero token.
        Buf::advance_bytes(&mut self.meta_copy.pos, 1);
        self.tok = Tok::Num("0");
    }

    fn num_signed(&mut self) {
        let i = self.meta_copy.byte_off + 1;
        let n = self.data_ref.len();
        if i == n && !self.meta_copy.is_eof {
            self.end();
        } else if i == n {
            self.err_lex(String::from(
                "expected '1'..'9' after '-' in signed number, got EOF",
            ));
        } else {
            let x = self.data_ref[i];
            match x {
                b'1'..=b'9' => self.num_integer(2),
                _ => self.err_lex(format!(
                    "expected '1'..'9' after '-' in signed number, got {}",
                    describe_octet(x)
                )),
            }
        }
    }

    fn num_integer(&mut self, offset: usize) {
        let mut i = self.meta_copy.byte_off + offset;
        let n = self.data_ref.len();
        loop {
            if i == n && !self.meta_copy.is_eof {
                self.end();
                return;
            } else if i == n {
                break;
            } else {
                let x = self.data_ref[i];
                match x {
                    b'0'..=b'9' => i += 1,
                    b'.' => return self.num_fraction(i - self.meta_copy.byte_off + 1),
                    b'e' | b'E' => return self.num_exponent(i - self.meta_copy.byte_off + 1),
                    b'{' | b'}' | b'[' | b']' | b',' | b':' | b'"' => break,
                    _ => {
                        return self.err_lex(format!(
                            "expected '0'..'9' in number integer part, got {}",
                            describe_octet(x)
                        ))
                    }
                }
            }
        }
        self.tok = Tok::Num(self.slice_unchecked(self.meta_copy.byte_off, i));
        Buf::advance_bytes(&mut self.meta_copy.pos, i - self.meta_copy.byte_off);
    }

    fn num_fraction(&mut self, offset: usize) {
        let mut i = self.meta_copy.byte_off + offset;
        let n = self.data_ref.len();
        // At least one digit is required in the fractional part.
        if i == n && !self.meta_copy.is_eof {
            self.end();
            return;
        } else if i == n {
            self.err_lex(String::from(
                "expected '0'..'9' in number fractional part, got EOF",
            ));
            return;
        }
        let x = self.data_ref[i];
        match x {
            b'0'..=b'9' => i += 1,
            _ => {
                self.err_lex(format!(
                    "expected '0'..'9' in number fractional part, got {}",
                    describe_octet(x)
                ));
                return;
            }
        }
        // Fetch remaining optional digits.
        loop {
            if i == n && !self.meta_copy.is_eof {
                self.end();
                return;
            } else if i == n {
                break;
            } else {
                let x = self.data_ref[i];
                match x {
                    b'0'..=b'9' => i += 1,
                    b'e' | b'E' => return self.num_exponent(i - self.meta_copy.byte_off + 1),
                    b'{' | b'}' | b'[' | b']' | b',' | b':' | b'"' => break,
                    _ => {
                        return self.err_lex(format!(
                            "expected '0'..'9' in number fractional part, got {}",
                            describe_octet(x)
                        ))
                    }
                }
            }
        }
        self.tok = Tok::Num(self.slice_unchecked(self.meta_copy.byte_off, i));
        Buf::advance_bytes(&mut self.meta_copy.pos, i - self.meta_copy.byte_off);
    }

    fn num_exponent(&mut self, offset: usize) {
        let mut i = self.meta_copy.byte_off + offset;
        let n = self.data_ref.len();
        // An optional +/- is allowed.
        if i == n && !self.meta_copy.is_eof {
            self.end();
            return;
        } else if i == n {
            self.err_lex(String::from(
                "expected '+', '-', or '0'..'9' in number exponent, got EOF",
            ));
            return;
        }
        let x = self.data_ref[i];
        match x {
            b'+' | b'-' => i += 1,
            b'0'..=b'9' => (),
            _ => self.err_lex(format!(
                "expected '+', '-', or '0'..'9' in number exponent, got {}",
                describe_octet(x)
            )),
        }
        // At least one digit is required.
        if i == n && !self.meta_copy.is_eof {
            self.end();
            return;
        } else if i == n {
            self.err_lex(String::from(
                "expected '0'..'9' in number exponent, got EOF",
            ));
            return;
        }
        let x = self.data_ref[i];
        match x {
            b'0'..=b'9' => i += 1,
            _ => self.err_lex(format!(
                "expected '0'..'9' in number exponent, got {}",
                describe_octet(x)
            )),
        }
        // Fetch remaining optional digits.
        loop {
            if i == n && !self.meta_copy.is_eof {
                self.end();
                return;
            } else if i == n {
                break;
            } else {
                let x = self.data_ref[i];
                match x {
                    b'0'..=b'9' => i += 1,
                    b'{' | b'}' | b'[' | b']' | b',' | b':' | b'"' => break,
                    _ => {
                        return self.err_lex(format!(
                            "expected '0'..'9' in number exponent, got {}",
                            describe_octet(x)
                        ))
                    }
                }
            }
        }
        self.tok = Tok::Num(self.slice_unchecked(self.meta_copy.byte_off, i));
        Buf::advance_bytes(&mut self.meta_copy.pos, i - self.meta_copy.byte_off);
    }

    fn key(&mut self, key: &'static [u8]) {
        let mut i = 1;
        let m = key.len();
        let mut j = self.meta_copy.byte_off + 1;
        let n = self.data_ref.len();
        loop {
            if j == n && !self.meta_copy.is_eof {
                // Need more imput.
                self.end();
                break;
            } else if j == n {
                // Lexical error: unexpected end of input while expecting keyword.
                self.err_lex(format!(
                    "unexpected end of input while expecting {} for keyword {}",
                    key[i] as char,
                    std::str::from_utf8(key).unwrap()
                ));
                break;
            } else if key[i] != self.data_ref[j] {
                // Lexical error: unexpected byte while expecting keyword.
                self.err_lex(format!(
                    "unexpected {} while expecting {} for keyword {}",
                    describe_octet(self.data_ref[j]),
                    key[i],
                    std::str::from_utf8(key).unwrap()
                ));
                break;
            } else if i + 1 < m {
                // Valid character.
                i = i + 1;
                j = j + 1;
            } else {
                // Keyword match.
                Buf::advance_bytes(&mut self.meta_copy.pos, m);
                self.tok = Tok::Key(unsafe { std::str::from_utf8_unchecked(key) });
                break;
            }
        }
    }

    fn white(&mut self) {
        let n = self.data_ref.len();
        let mut i = self.meta_copy.byte_off;
        let mut j = i;
        let mut pos = self.meta_copy.pos;
        loop {
            let x = self.data_ref[j];
            match x {
                b'\t' | b' ' => {
                    j = j + 1;
                }
                b'\n' => {
                    j = j + 1;
                    Buf::advance_line(&mut pos, j - i);
                    i = j;
                }
                b'\r' => {
                    if j + 1 < n && self.data_ref[j + 1] == b'\n' {
                        // Treat CR/LF pair as a new line.
                        j = j + 2;
                        Buf::advance_line(&mut pos, j - i);
                        i = j;
                    } else if j + 1 < n || self.meta_copy.is_eof {
                        // Treat CR by itself as a new line.
                        j = j + 1;
                        Buf::advance_line(&mut pos, j - i);
                        i = j;
                    } else {
                        // CR is at the end of buffer. Wait for more input to handle it.
                        self.end();
                        return;
                    }
                }
                _ => {
                    Buf::advance_bytes(&mut pos, j - i);
                    self.meta_copy.pos = pos;
                    self.tok = Tok::White(self.slice_unchecked(self.meta_copy.byte_off, j));
                    return;
                }
            }
            if j == n {
                self.end();
                return;
            }
        }
    }

    fn end(&mut self) {
        self.tok = Tok::End(self.slice_unchecked(self.meta_copy.byte_off, self.data_ref.len()));
        self.meta_copy.is_consumed = true;
    }

    fn err_lex(&mut self, desc: String) {
        self.err(Error {
            cat: ErrorCat::Lex,
            desc: desc,
            pos: self.meta_copy.pos,
            source: None,
        })
    }

    fn err(&mut self, err: Error) {
        self.tok = Tok::Err(err);
        self.meta_copy.is_consumed = true;
    }

    fn advance_bytes(pos: &mut Pos, num_bytes: usize) {
        pos.byte_off += num_bytes as u64;
        pos.byte_off += num_bytes as u64;
        pos.col += num_bytes as u64;
    }

    fn advance_line(pos: &mut Pos, num_bytes: usize) {
        pos.byte_off += num_bytes as u64;
        pos.col = 0;
        pos.line += 1;
    }

    fn slice_unchecked(&self, i: usize, j: usize) -> &'a str {
        let slice = &self.data_ref[i..j];
        unsafe { std::str::from_utf8_unchecked(slice) }
    }

    //fn str(&self, )
}

impl<'a> Drop for Buf<'a> {
    fn drop(&mut self) {
        let mut meta = self.shared.meta.borrow_mut();
        *meta = self.meta_copy.clone();
    }
}

// impl<R> Stream for Lex<R>
// where
//     R: Read,
// {
//     fn next(&mut self) -> Option<impl Buf> {
//         // Logic:
//         // 1) If there is a buffer out in use, we panic and say it needs to be
//         //    returned.
//         // 2) If there is no buffer at all, we have to allocate it.
//         // 3) Upon being returned (elsewhere), if buffer was NOT fully used then
//         //    we are quietly put into an error state that will trigger a panic
//         //    here. If it was fully used, then incomplete remainder is now copied
//         //    to the front of the buffer. If incomplete remaindert WAS at the
//         //    front of the buffer, then we have to allocate a bigger buffer.
//     }

//     fn pos(&self) -> Pos {
//         self.pos
//     }
// }

fn describe_octet(octet: u8) -> String {
    match octet {
        b'\t' => String::from("control character 0x09 ('\t')"),
        b'\n' => String::from("control character 0x0a ('\n')"),
        b'\r' => String::from("control character 0x0a ('\r')"),
        0..b' ' => format!("control characer 0x{:02x}", octet),
        b' '..0x80 => format!("character '{}'", octet as char),
        _ => format!("octet 0x{:02x}", octet),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
