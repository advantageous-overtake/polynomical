use std::{
    collections::HashMap,
    hash::Hash,
    ops::{Add, Mul},
};

use num::{
    traits::{WrappingAdd, WrappingMul, WrappingNeg, WrappingSub},
    Integer,
};

macro_rules! debuggable {
    [$($target_item:item)+] => {
        $(
            #[cfg_attr(any(test, debug_assertions), derive(Debug))]
            $target_item
        )+
    };
}

pub trait Operable:
    Integer + WrappingAdd + WrappingMul + WrappingSub + WrappingNeg + Clone + Copy + Hash
{
}

impl<T> Operable for T where
    T: Integer + WrappingAdd + WrappingMul + WrappingSub + WrappingNeg + Clone + Copy + Hash
{
}

#[macro_export]
macro_rules! polynomial {
    ((x $(+)? $l0:literal)$((x $(+)? $li:literal))*) => {
        {

           let p0 = Polynomial::new(&[monomial!(x), monomial!($l0)]);


            [
                $(Polynomial::new(&[monomial!(x), monomial!($li)])),*
            ]
            .into_iter()
            .map( | p0 | p0.into() )
            .fold(p0, | p0, p1 | p0 * p1)
            .into()
        }
    };
}

#[macro_export]
macro_rules! monomial {
    (x) => {
        Monomial::unit()
    };
    ($k0:literal) => {
        Monomial::independient($k0)
    };
    ($k0:literal x) => {
        Monomial::from_coefficient($k0)
    };
    ($k0:literal x ^ $k1:literal) => {
        Monomial::from_pair(($k0, $k1))
    };
    (x ^ $k0:literal) => {
        Monomial::from_grade($k0)
    };
}

debuggable! {
    pub enum Expr<T>
    where
        T: Operable,
    {
        Polynomial(Polynomial<T>),
        Monomial(Monomial<T>),
    }

    #[derive(Clone, Copy, PartialEq)]
    pub struct Monomial<T>
    where
        T: Operable,
    {
        coefficient: T,
        grade: T,
    }

    pub struct Polynomial<T>(pub Vec<Monomial<T>>)
    where
        T: Operable;
}

impl<T: Operable> TryFrom<Expr<T>> for Monomial<T> {
    type Error = ();
    fn try_from(value: Expr<T>) -> Result<Self, Self::Error> {
        match value {
            Expr::Monomial(m0) => Ok(m0),
            _ => Err(()),
        }
    }
}

impl<T: Operable> TryFrom<Expr<T>> for Polynomial<T> {
    type Error = ();
    fn try_from(value: Expr<T>) -> Result<Self, Self::Error> {
        match value {
            Expr::Polynomial(p0) => Ok(p0),
            _ => Err(()),
        }
    }
}

impl<T: Operable> From<Monomial<T>> for Expr<T> {
    #[inline(always)]
    fn from(value: Monomial<T>) -> Self {
        Self::Monomial(value)
    }
}

impl<T: Operable> From<Polynomial<T>> for Expr<T> {
    #[inline(always)]
    fn from(value: Polynomial<T>) -> Self {
        Self::Polynomial(value)
    }
}

impl<T: Operable> Monomial<T> {
    #[inline(always)]
    pub fn independient(coefficient: T) -> Self {
        Self {
            coefficient,
            grade: T::zero(),
        }
    }

    #[inline(always)]
    pub fn unit() -> Self {
        Self {
            coefficient: T::one(),
            grade: T::one(),
        }
    }

    #[inline(always)]
    pub fn from_coefficient(coefficient: T) -> Self {
        Self {
            coefficient,
            grade: T::one(),
        }
    }

    #[inline(always)]
    pub fn from_grade(grade: T) -> Self {
        Self {
            coefficient: T::one(),
            grade,
        }
    }

    #[inline(always)]
    pub fn from_pair(pair: (T, T)) -> Self {
        Self {
            coefficient: pair.0,
            grade: pair.1,
        }
    }
}

impl<T: Operable> Polynomial<T> {
    #[inline(always)]
    pub fn new(value: &[Monomial<T>]) -> Self {
        Self(value.to_vec())
    }

    #[inline(always)]
    pub fn inner_mut(&mut self) -> &mut Vec<Monomial<T>> {
        &mut self.0
    }
    #[inline(always)]
    pub fn inner(&self) -> &Vec<Monomial<T>> {
        &self.0
    }
    #[inline(always)]
    pub fn into_inner(self) -> Vec<Monomial<T>> {
        self.0
    }
    #[inline(always)]
    pub fn ordered(self) -> Self {
        let mut grade_hash: HashMap<T, Vec<Monomial<T>>> = HashMap::new();

        for monomial in self.into_inner().into_iter() {
            grade_hash
                .entry(monomial.grade)
                .or_insert(vec![])
                .push(monomial);
        }

        {
            let mut monomial_vec = grade_hash.into_iter().collect::<Vec<_>>();

            monomial_vec.sort_by(|(g0, _), (g1, _)| g1.cmp(g0));

            monomial_vec
                .into_iter()
                .map(|(_, mv0)| {
                    Monomial::from_pair(
                        mv0.into_iter()
                            .map(|m0| (m0.coefficient, m0.grade))
                            .fold((T::zero(), T::zero()), |(c0, _), (c1, g1)| (c0 + c1, g1)),
                    )
                })
                .filter(|m0| m0.coefficient != T::zero())
        }
        .collect::<Polynomial<_>>()
    }
}

impl<P: Operable> FromIterator<Monomial<P>> for Polynomial<P> {
    fn from_iter<T: IntoIterator<Item = Monomial<P>>>(iter: T) -> Self {
        Self(iter.into_iter().collect::<Vec<Monomial<P>>>())
    }
}

macro_rules! operator_fn_impl {
    ($target_op:ident as { Polynomial <-> Polynomial => $poly_expr:expr, Monomial <-> Monomial => $mono_expr:expr, Mixed => $mixed_expr:expr }) => {
        #[inline]
        fn $target_op(self, rhs: Self) -> Self {
            #[inline(always)]
            fn handle_poly<T: Operable>(p0: Polynomial<T>, p1: Polynomial<T>) -> Expr<T> {
                {
                    ($poly_expr as fn((Polynomial<T>, Polynomial<T>)) -> Expr<T>)((p0, p1))
                }
            }

            #[inline(always)]
            fn handle_mono<T: Operable>(m0: Monomial<T>, m1: Monomial<T>) -> Expr<T> {
                {
                    ($mono_expr as fn((Monomial<T>, Monomial<T>)) -> Expr<T>)((m0, m1))
                }
            }

            #[inline(always)]
            fn handle_mixed<T: Operable>(p0: Polynomial<T>, m0: Monomial<T>) -> Expr<T> {
                {
                    ($mixed_expr as fn((Polynomial<T>, Monomial<T>)) -> Expr<T>)((p0, m0))
                }
            }

            match self {
                Expr::Polynomial(p0) => match rhs {
                    Expr::Polynomial(p1) => handle_poly(p0, p1).into(),
                    Expr::Monomial(m0) => handle_mixed(p0, m0).into(),
                },
                Expr::Monomial(m0) => match rhs {
                    Expr::Polynomial(p0) => handle_mixed(p0, m0).into(),
                    Expr::Monomial(m1) => handle_mono(m0, m1).into(),
                },
            }
        }
    };
}

macro_rules! operator_impl {
        (impl $target_trait:ident for $target_item:ty as { $($target_tt:tt)+ }) => {
            ::paste::paste! {
                impl<T: Operable> $target_trait for $target_item {
                    type Output = Self;
                     operator_fn_impl!{
                         [< $target_trait:lower >] as { $($target_tt)+ }
                     }
                }
            }
        };
        (impl $target_trait:ident for $target_item:ty => $target_expr:expr) => {
            ::paste::paste! {
                impl<T: Operable> $target_trait for $target_item {
                    type Output = Self;

                    fn [< $target_trait:lower >](self, rhs: Self) -> Self::Output {
                        ($target_expr as fn((Self, Self)) -> Self)((self, rhs))
                    }
                }
            }
        };
    }

operator_impl!(impl Add for Expr<T> as {
    Polynomial <-> Polynomial => | (mut p0, p1) | {
        p0
            .inner_mut()
            .extend(p1.into_inner().into_iter());

        p0
            .ordered()
            .into()
    },
    Monomial   <-> Monomial   => | (m0, m1) | Polynomial(vec![m0, m1]).into(),
    Mixed                     => | (mut p0, m0) | {
        p0
            .inner_mut()
            .push(m0);

        p0
            .ordered()
            .into()
    }
});

operator_impl!(impl Mul for Expr<T> as {
    Polynomial <-> Polynomial => | (p0, p1) | {
        p0
            .into_inner()
            .into_iter()
            .flat_map(| m0 | p1
                .inner()
                .iter()
                .map( | m1 | m0 * *m1 )
                .collect::<Vec<Monomial<_>>>())
            .collect::<Polynomial<_>>()
            .ordered()
            .into()
    },
    Monomial   <-> Monomial   => | (m0, m1) | {
        (m0 * m1).into()
    },
    Mixed                     => | (p0, m0) | {
        p0
            .into_inner()
            .into_iter()
            .map( | m1 | m0 * m1 )
            .collect::<Polynomial<_>>()
            .ordered()
            .into()
    }
});

operator_impl!(impl Add for Polynomial<T> => | (p0, p1) | {

    let (p0, p1): (Expr<_>, Expr<_>) = (p0.into(), p1.into());


    let p2 = p0 + p1;
    // SAFETY: `p2` is guaranteed to be the Expr<_>::Polynomial(_) variant.
    unsafe {
        p2
            .try_into()
            .unwrap_unchecked()
    }
});

operator_impl!(impl Mul for Monomial<T> => | (mut m0, m1) | {
        m0.grade = m0.grade.wrapping_add(&m1.grade);
        m0.coefficient = m0.coefficient.wrapping_mul(&m1.coefficient);

        m0.into()
});

operator_impl!(impl Mul for Polynomial<T> => | (p0, p1) | {

    let (p0, p1): (Expr<_>, Expr<_>) = (p0.into(), p1.into());


    let p2 = p0 * p1;
    // SAFETY: `p2` is guaranteed to be the Expr<_>::Polynomial(_) variant.
    unsafe {
        p2
            .try_into()
            .unwrap_unchecked()
    }
});

#[cfg(test)]
mod tests {
    use super::{Expr, Monomial, Polynomial};

    #[test]
    fn add_monomial0() {
        let m0: Expr<usize> = monomial!(2 x ^ 2).into();
        let m1 = monomial!(4 x ^ 3).into();

        let p0 = m0 + m1;

        assert!(matches!(p0, Expr::Polynomial(_)));

        assert_eq!(
            &[monomial!(4 x ^ 3), monomial!(2 x ^ 2)],
            <Expr<_> as TryInto<Polynomial<_>>>::try_into(p0)
                .unwrap()
                .ordered()
                .into_inner()
                .as_slice()
        );
    }

    #[test]
    fn add_monomial1() {
        let m0: Expr<usize> = monomial!(2 x ^ 2).into();
        let m1 = monomial!(4 x ^ 2).into();

        let p0 = m0 + m1;

        assert!(matches!(p0, Expr::Polynomial(_)));

        assert_eq!(
            &[monomial!(6 x ^ 2)],
            <Expr<_> as TryInto<Polynomial<_>>>::try_into(p0)
                .unwrap()
                .ordered()
                .into_inner()
                .as_slice()
        );
    }

    #[test]
    fn mul_monomial0() {
        let m0: Monomial<usize> = monomial!(16 x ^ 2);
        let m1 = monomial!(4 x ^ 7);

        let m2 = m0 * m1;

        assert_eq!(monomial!(64 x ^ 9), m2);
    }

    #[test]
    fn mul_monomial1() {
        let m0: Monomial<usize> = monomial!(2 x ^ 2);
        let m1 = monomial!(4 x ^ 2);

        let m2 = m0 * m1;

        assert_eq!(monomial!(8 x ^ 4), m2);
    }

    #[test]
    fn add_polynomial0() {
        let p0: Polynomial<isize> = polynomial!((x - 1)(x - 2)(x - 3));
        let p1 = polynomial!((x - 5)(x - 8)(x - 0));

        let p3 = p0 + p1;

        assert_eq!(
            &[
                monomial!(2 x ^ 3),
                monomial!(-19 x ^ 2),
                monomial!(51 x),
                monomial!(-6),
            ],
            p3.ordered().into_inner().as_slice()
        );
    }

    #[test]
    fn add_polynomial1() {
        let p0: Polynomial<isize> = polynomial!((x - 192)(x  31)(x - 9)(x - 12));
        let p1: Polynomial<isize> = polynomial!((x - 14)(x - 46)(x - 2)(x - 7)(x - 0));

        let p3 = p0 + p1;

        assert_eq!(
            &[
                monomial!(x ^ 5),
                monomial!(-68 x ^ 4),
                monomial!(1016 x ^ 3),
                monomial!(-9099 x ^ 2),
                monomial!(116620 x),
                monomial!(-642816)
            ],
            p3.ordered().into_inner().as_slice()
        );
    }

    #[test]
    fn mul_polynomial0() {
        let p0: Polynomial<isize> = polynomial!((x - 1)(x - 2)(x - 3));
        let p1 = polynomial!((x - 5)(x - 8)(x - 0));

        let p3 = p0 * p1;

        assert_eq!(
            &[
                monomial!(x ^ 6),
                monomial!(-19 x ^ 5),
                monomial!(129 x ^ 4),
                monomial!(-389 x ^ 3),
                monomial!(518 x ^ 2),
                monomial!(-240 x),
            ],
            p3.ordered().into_inner().as_slice()
        );
    }

    #[test]
    fn mul_polynomial1() {
        let p0: Polynomial<isize> = polynomial!((x - 192)(x + 31)(x - 9)(x - 12));
        let p1 = polynomial!((x - 14)(x - 46)(x - 2)(x - 7)(x - 0));

        let p3 = p0 * p1;

        assert_eq!(
            &[
                monomial!(x ^ 9),
                monomial!(-251 x ^ 8),
                monomial!(11293 x ^ 7),
                monomial!(52879 x ^ 6),
                monomial!(-9801398 x ^ 5),
                monomial!(187967452 x ^ 4),
                monomial!(-1506360120 x ^ 3),
                monomial!( 5235884640 x ^ 2),
                monomial!(-5795629056 x)
            ],
            p3.ordered().into_inner().as_slice()
        );
    }

    #[test]
    fn root_polynomial0() {
        let p0: Polynomial<isize> = polynomial!((x - 1)(x - 2)(x - 3));

        assert_eq!(
            &[
                monomial!(x ^ 3),
                monomial!(-6 x ^ 2),
                monomial!(11 x),
                monomial!(-6)
            ],
            p0.ordered().into_inner().as_slice()
        );
    }

    #[test]
    fn root_polynomial1() {
        let p0: Polynomial<isize> = polynomial!((x - 9)(x - 6)(x - 4)(x + 2));

        assert_eq!(
            &[
                monomial!(x ^ 4),
                monomial!(-17 x ^ 3),
                monomial!(76 x ^ 2),
                monomial!(12 x),
                monomial!(-432)
            ],
            p0.ordered().into_inner().as_slice()
        );
    }
}
