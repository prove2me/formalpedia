-- Prove2me | solution 1 for DeciSigma1.Arithmetic.iterate_exp2_mono_height
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:07:38.345936+00:00
-- url     : https://prove2.me/submissions/125207f7-73f3-4e53-8370-978254ac3632

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_le_exp2

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (x : ℕ) : Monotone (fun h => exp2^[h] x) :=
  exp2_mono.monotone_iterate_of_le_map (le_exp2 x)
end DeciSigma1.Arithmetic
