-- Prove2me | solution 1 for BooleanIsoperimetry.HIncrement_window_le_of_gShiftIntervalCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:22.400111+00:00
-- url     : https://prove2.me/submissions/fcb9f4e2-56dc-481d-a317-b297c8540d6e

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
public import Theorems.Thm_BooleanIsoperimetry_HIncrement_window_eq_gShiftIntervalCount

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    {n lo₁ hi₁ lo₂ hi₂ slack : ℕ}
    (h₁ : lo₁ ≤ hi₁) (h₂ : lo₂ ≤ hi₂)
    (hcount :
      gShiftIntervalCount n lo₁ hi₁ ≤ gShiftIntervalCount n lo₂ hi₂ + slack) :
    (∑ i ∈ Finset.Ico lo₁ hi₁, HIncrement n i) ≤
      (∑ i ∈ Finset.Ico lo₂ hi₂, HIncrement n i) + slack := by
  rw [HIncrement_window_eq_gShiftIntervalCount n lo₁ hi₁ h₁,
      HIncrement_window_eq_gShiftIntervalCount n lo₂ hi₂ h₂]
  exact hcount
end BooleanIsoperimetry
