-- Prove2me | solution 1 for DeciSigma1.Arithmetic.le_iterate_exp2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:24.442484+00:00
-- url     : https://prove2.me/submissions/2747a9b3-ed37-400a-ba38-ffad69d12bff

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_le_exp2

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (h x : ℕ) : x ≤ exp2^[h] x := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_exp2 _)
end DeciSigma1.Arithmetic
