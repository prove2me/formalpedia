-- Prove2me | solution 1 for DeciSigma1.Arithmetic.exp2_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:08.73269+00:00
-- url     : https://prove2.me/submissions/8b70f077-61a3-4b09-a7ba-6e6aab19f200

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (a b : ℕ) : exp2 a + exp2 b ≤ exp2 (a + b + 1) := by
  have ha := exp2_mono (Nat.le_add_right a b)
  have hb := exp2_mono (Nat.le_add_left b a)
  rw [exp2_add (a + b) 1]
  change exp2 a + exp2 b ≤ exp2 (a + b) * 2
  omega
end DeciSigma1.Arithmetic
