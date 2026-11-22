-- Prove2me | solution 1 for DeciSigma1.Arithmetic.succ_le_exp2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:36:07.396962+00:00
-- url     : https://prove2.me/submissions/6b9cfd3c-b2c9-403a-8f63-7560df06e42c

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
namespace DeciSigma1.Arithmetic
theorem _root_.solution (x : ℕ) : x + 1 ≤ exp2 x := Nat.lt_two_pow_self
end DeciSigma1.Arithmetic
