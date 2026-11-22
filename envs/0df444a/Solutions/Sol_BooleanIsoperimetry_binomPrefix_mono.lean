-- Prove2me | solution 1 for BooleanIsoperimetry.binomPrefix_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:57.006781+00:00
-- url     : https://prove2.me/submissions/edbc5143-ef49-402e-be61-5e4d28cb231c

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) {r s : ℕ} (h : r ≤ s) :
    binomPrefix n r ≤ binomPrefix n s := by
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)
end BooleanIsoperimetry
