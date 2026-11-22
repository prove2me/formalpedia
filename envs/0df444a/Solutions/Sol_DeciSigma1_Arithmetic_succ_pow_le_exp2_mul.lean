-- Prove2me | solution 1 for DeciSigma1.Arithmetic.succ_pow_le_exp2_mul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T15:03:54.165558+00:00
-- url     : https://prove2.me/submissions/de60844b-2868-412d-977e-403b87a24edf

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
theorem DeciSigma1.Arithmetic.succ_pow_le_exp2_mul (x d : ℕ) : (x + 1) ^ d ≤ exp2 (d * x) := by
  unfold exp2
  have h : x + 1 ≤ 2 ^ x := Nat.lt_two_pow_self
  calc (x + 1) ^ d ≤ (2 ^ x) ^ d := Nat.pow_le_pow_left h d
    _ = 2 ^ (d * x) := by rw [← pow_mul, Nat.mul_comm]

theorem solution (x d : ℕ) : (x + 1) ^ d ≤ exp2 (d * x) :=
  DeciSigma1.Arithmetic.succ_pow_le_exp2_mul x d
