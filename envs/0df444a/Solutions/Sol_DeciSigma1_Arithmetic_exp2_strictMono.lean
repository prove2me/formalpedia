-- Prove2me | solution 1 for DeciSigma1.Arithmetic.exp2_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:40:56.621069+00:00
-- url     : https://prove2.me/submissions/af416446-9609-4db0-88b4-812da3f0b90a

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
theorem _root_.solution : StrictMono exp2 := by
  intro a b h
  exact Nat.pow_lt_pow_right (by decide) h
end DeciSigma1.Arithmetic
