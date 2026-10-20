-- Prove2me | solution 1 for DerivativeChainPrivate.weighted_real_root_count
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T05:00:17.877921+00:00
-- url     : https://prove2.me/submissions/7483353d-ffdf-469b-9ae3-68dcafec8fbf

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial



theorem weighted_derivative_factor (q : Polynomial ℝ) (r k : ℕ) :
    (X ^ (r + 1) * q ^ (k + 1)).derivative =
      X ^ r * q ^ k * (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative) := by
  simp only [derivative_mul, derivative_pow, derivative_X, mul_one,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [pow_succ q k, pow_succ X r]
  ring











end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate









end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (q : Polynomial ℝ) (hq : q ≠ 0) (r k : ℕ) :
    let b := C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
    b.natDegree = q.natDegree ∧ q.roots.card ≤ b.roots.card := by
  classical
  dsimp only
  let b := C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
  let p := X ^ (r + 1) * q ^ (k + 1)
  have hpdeg : p.natDegree = r + 1 + (k + 1) * q.natDegree := by
    dsimp [p]
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq),
      natDegree_X_pow, natDegree_pow]
  have hd : p.derivative ≠ 0 := by
    intro h
    have hz := Polynomial.derivative_eq_zero.mp h
    rw [hpdeg] at hz
    omega
  have hb : b ≠ 0 := by
    intro h
    apply hd
    rw [show p.derivative = X ^ r * q ^ k * b from weighted_derivative_factor q r k, h]
    simp
  have hfactor : p.derivative = X ^ r * q ^ k * b := weighted_derivative_factor q r k
  have hbdeg : b.natDegree = q.natDegree := by
    have heq := congrArg Polynomial.natDegree hfactor
    rw [Polynomial.natDegree_derivative, hpdeg,
      natDegree_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq)) hb,
      natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq),
      natDegree_X_pow, natDegree_pow] at heq
    simp only [Nat.add_mul, Nat.one_mul] at heq
    omega
  have hcount := p.card_roots_le_derivative
  have hpne : p ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq)
  have hpcount : p.roots.card = r + 1 + (k + 1) * q.roots.card := by
    dsimp [p]
    rw [roots_mul hpne, Multiset.card_add, roots_X_pow, Multiset.card_nsmul, Multiset.card_singleton, mul_one,
      roots_pow, Multiset.card_nsmul]
  have hdcount : p.derivative.roots.card = r + k * q.roots.card + b.roots.card := by
    rw [hfactor, roots_mul (by rw [← hfactor]; exact hd), Multiset.card_add,
      roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq)),
      Multiset.card_add, roots_X_pow, Multiset.card_nsmul, Multiset.card_singleton, mul_one,
      roots_pow, Multiset.card_nsmul]
  refine ⟨hbdeg, ?_⟩
  rw [hpcount, hdcount] at hcount
  nlinarith
