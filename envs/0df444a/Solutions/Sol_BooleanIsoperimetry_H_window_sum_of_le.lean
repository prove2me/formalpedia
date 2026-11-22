-- Prove2me | solution 1 for BooleanIsoperimetry.H_window_sum_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:42.441985+00:00
-- url     : https://prove2.me/submissions/43cd8182-ce79-4a8e-9de8-71b06debe14b

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_H_eq_sum_HIncrement


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n lo hi : ℕ) (hlohi : lo ≤ hi) :
    H n hi = H n lo + ∑ i ∈ Finset.Ico lo hi, HIncrement n i := by
  have h1 := H_eq_sum_HIncrement n hi
  have h2 := H_eq_sum_HIncrement n lo
  rw [h1, h2]
  rw [← Finset.sum_range_add_sum_Ico (f := fun i => HIncrement n i) hlohi]
end BooleanIsoperimetry
