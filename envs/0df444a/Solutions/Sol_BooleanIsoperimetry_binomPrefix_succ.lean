-- Prove2me | solution 1 for BooleanIsoperimetry.binomPrefix_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:11.574537+00:00
-- url     : https://prove2.me/submissions/8fac614f-f25b-4a64-93f6-8c27fda6e81c

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
theorem _root_.solution (n r : ℕ) :
    binomPrefix n (r + 1) = binomPrefix n r + Nat.choose n r := by
  simp [binomPrefix, Finset.sum_range_succ]
end BooleanIsoperimetry
