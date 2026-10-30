-- Prove2me | solution 1 for DerivativeChainPrivate.real_splits_weighted_derivative
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:51:13.164829+00:00
-- url     : https://prove2.me/submissions/6ced230e-6a26-4a91-9dbc-37dd4fed36cc

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial

theorem real_splits_derivative (p : Polynomial ℝ) (hp : p.Splits) :
    p.derivative.Splits := by
  apply Polynomial.splits_iff_card_roots.mpr
  have hcount := p.card_roots_le_derivative
  have hdegree := Polynomial.natDegree_derivative p
  have hbound := Polynomial.card_roots' p.derivative
  have hsplit := hp.natDegree_eq_card_roots
  omega

theorem weighted_derivative_factor (q : Polynomial ℝ) (r k : ℕ) :
    (X ^ (r + 1) * q ^ (k + 1)).derivative =
      X ^ r * q ^ k * (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative) := by
  simp only [derivative_mul, derivative_pow, derivative_X, mul_one,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [pow_succ q k, pow_succ X r]
  ring











end DerivativeChainPrivate



set_option autoImplicit false

open DerivativeChainPrivate
open Polynomial





theorem solution (q : Polynomial ℝ) (hq : q.Splits)
    (r k : ℕ) :
    (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).Splits := by
  by_cases hqzero : q = 0
  · simp [hqzero, Polynomial.Splits.zero]
  let b : Polynomial ℝ := C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
  by_cases hb : b = 0
  · simpa only [b, hb] using (Polynomial.Splits.zero : (0 : Polynomial ℝ).Splits)
  have hs := _root_.DerivativeChainPrivate.real_splits_derivative (X ^ (r + 1) * q ^ (k + 1))
    ((Polynomial.Splits.X_pow (r + 1)).mul (hq.pow (k + 1)))
  rw [_root_.DerivativeChainPrivate.weighted_derivative_factor] at hs
  have hne : X ^ r * q ^ k * b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hqzero)) hb
  exact hs.of_dvd hne ⟨X ^ r * q ^ k, by ring⟩
