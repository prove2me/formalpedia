-- Prove2me | solution 1 for DeciSigma1.Arithmetic.le_exp2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:36:32.090059+00:00
-- url     : https://prove2.me/submissions/ed9eb3a9-913d-4c48-acfc-91be1dca8ac8

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_succ_le_exp2

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (x : ℕ) : x ≤ exp2 x := (Nat.le_succ x).trans (succ_le_exp2 x)
end DeciSigma1.Arithmetic
