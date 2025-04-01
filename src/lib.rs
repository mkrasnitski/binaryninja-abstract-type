#[doc(hidden)]
pub use elain;

use binaryninja::rc::Ref;
use binaryninja::types::Type;
use std::alloc::Layout;

pub use binaryninja_abstract_type_derive::AbstractType;

pub trait AbstractType: Sized {
    #[doc(hidden)]
    const LAYOUT: Layout = Layout::new::<Self>();

    fn resolve_type() -> Ref<Type>;
}

macro_rules! abstract_type {
    ($($t:ty => $e:expr),+) => {
        $(
            impl AbstractType for $t {
                fn resolve_type() -> Ref<Type> {
                    $e
                }
            }
        )+
    }
}

abstract_type! {
    u8 => Type::int(1, false),
    u16 => Type::int(2, false),
    u32 => Type::int(4, false),
    u64 => Type::int(8, false),
    u128 => Type::int(16, false),
    i8 => Type::int(1, true),
    i16 => Type::int(2, true),
    i32 => Type::int(4, true),
    i64 => Type::int(8, true),
    i128 => Type::int(16, true),
    f32 => Type::float(4),
    f64 => Type::float(8)
}

impl<T: AbstractType, const N: usize> AbstractType for [T; N] {
    fn resolve_type() -> Ref<Type> {
        Type::array(&T::resolve_type(), N as u64)
    }
}
