-- Prove2me | solution 1 for BooleanIsoperimetry.binomPrefix_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:40.326933+00:00
-- url     : https://prove2.me/submissions/7cc79468-55eb-4d9e-a25c-4ee651d61495

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) : binomPrefix n (n + 1) = 2 ^ n := by
  simpa [binomPrefix] using Nat.sum_range_choose n
end BooleanIsoperimetry
