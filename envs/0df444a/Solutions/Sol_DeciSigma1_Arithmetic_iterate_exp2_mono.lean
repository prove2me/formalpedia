-- Prove2me | solution 1 for DeciSigma1.Arithmetic.iterate_exp2_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:01.13631+00:00
-- url     : https://prove2.me/submissions/ef7b614b-542c-42f0-92c1-ecc9a9797534

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (h : ℕ) : Monotone (exp2^[h]) := exp2_mono.iterate h
end DeciSigma1.Arithmetic
