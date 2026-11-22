-- Prove2me | solution 1 for DeciSigma1.Arithmetic.exp2_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:53.640011+00:00
-- url     : https://prove2.me/submissions/fa1477a3-f3c5-4d80-9efe-c50facb5a016

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_strictMono

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution : Monotone exp2 := exp2_strictMono.monotone
end DeciSigma1.Arithmetic
