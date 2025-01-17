#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
extern crate std;

extern "C" {
    fn __assert_fail(
        __assertion: *const std::os::raw::c_char,
        __file: *const std::os::raw::c_char,
        __line: std::os::raw::c_uint,
        __function: *const std::os::raw::c_char,
    ) -> !;
}
pub type size_t = std::os::raw::c_uint;
pub type __uint8_t = std::os::raw::c_uchar;
pub type __uint32_t = std::os::raw::c_uint;
pub type uint8_t = __uint8_t;
pub type uint32_t = __uint32_t;
pub type crypto_word = uint32_t;
pub type Limb = crypto_word;
#[no_mangle]
pub unsafe extern "C" fn little_endian_bytes_from_scalar(
    str: *mut uint8_t,
    str_len: size_t,
    scalar: *const Limb,
    num_limbs: size_t,
) {
    if str_len
        == num_limbs
            .wrapping_mul(std::mem::size_of::<Limb>() as u32)
            .wrapping_add(1 as std::os::raw::c_int as std::os::raw::c_uint)
    {
    } else {
        __assert_fail(
            b"str_len == (num_limbs * sizeof(Limb)) + 1\0" as *const u8
                as *const std::os::raw::c_char,
            b"crypto/fipsmodule/ec_17/ecp_nistz.c\0" as *const u8 as *const std::os::raw::c_char,
            31 as std::os::raw::c_int as std::os::raw::c_uint,
            (*std::mem::transmute::<&[u8; 78], &[std::os::raw::c_char; 78]>(
                b"void little_endian_bytes_from_scalar(uint8_t *, size_t, const Limb *, size_t)\0",
            ))
            .as_ptr(),
        );
    }
    let mut i: size_t;
    i = 0 as std::os::raw::c_int as size_t;
    while i < num_limbs.wrapping_mul(std::mem::size_of::<Limb>() as u32) {
        let mut d: Limb =
            *scalar.offset(i.wrapping_div(std::mem::size_of::<Limb>() as u32) as isize);
        *str.offset(i.wrapping_add(0 as std::os::raw::c_int as std::os::raw::c_uint) as isize) =
            (d & 0xff as std::os::raw::c_int as std::os::raw::c_uint) as uint8_t;
        *str.offset(i.wrapping_add(1 as std::os::raw::c_int as std::os::raw::c_uint) as isize) =
            (d >> 8 as std::os::raw::c_int & 0xff as std::os::raw::c_int as std::os::raw::c_uint)
                as uint8_t;
        *str.offset(i.wrapping_add(2 as std::os::raw::c_int as std::os::raw::c_uint) as isize) =
            (d >> 16 as std::os::raw::c_int & 0xff as std::os::raw::c_int as std::os::raw::c_uint)
                as uint8_t;
        d >>= 24 as std::os::raw::c_int;
        *str.offset(i.wrapping_add(3 as std::os::raw::c_int as std::os::raw::c_uint) as isize) =
            (d & 0xff as std::os::raw::c_int as std::os::raw::c_uint) as uint8_t;
        if std::mem::size_of::<Limb>() as u32 == 8 as std::os::raw::c_int as std::os::raw::c_uint {
            d >>= 8 as std::os::raw::c_int;
            *str.offset(
                i.wrapping_add(4 as std::os::raw::c_int as std::os::raw::c_uint) as isize,
            ) = (d & 0xff as std::os::raw::c_int as std::os::raw::c_uint) as uint8_t;
            *str.offset(
                i.wrapping_add(5 as std::os::raw::c_int as std::os::raw::c_uint) as isize,
            ) = (d >> 8 as std::os::raw::c_int
                & 0xff as std::os::raw::c_int as std::os::raw::c_uint) as uint8_t;
            *str.offset(
                i.wrapping_add(6 as std::os::raw::c_int as std::os::raw::c_uint) as isize,
            ) = (d >> 16 as std::os::raw::c_int
                & 0xff as std::os::raw::c_int as std::os::raw::c_uint) as uint8_t;
            *str.offset(
                i.wrapping_add(7 as std::os::raw::c_int as std::os::raw::c_uint) as isize,
            ) = (d >> 24 as std::os::raw::c_int
                & 0xff as std::os::raw::c_int as std::os::raw::c_uint) as uint8_t;
        }
        i = (i as std::os::raw::c_uint).wrapping_add(std::mem::size_of::<Limb>() as u32) as size_t
            as size_t;
    }
    while i < str_len {
        *str.offset(i as isize) = 0 as std::os::raw::c_int as uint8_t;
        i = i.wrapping_add(1);
    }
}
