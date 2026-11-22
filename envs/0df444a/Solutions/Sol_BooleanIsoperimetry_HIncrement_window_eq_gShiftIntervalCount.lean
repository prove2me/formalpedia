-- Prove2me | solution 1 for BooleanIsoperimetry.HIncrement_window_eq_gShiftIntervalCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:25.78157+00:00
-- url     : https://prove2.me/submissions/d9ad8775-cb9d-408d-9395-60758adcb3df

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
public import Theorems.Thm_BooleanIsoperimetry_H_window_sum_of_le
public import Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_eq_H_sub
public import Theorems.Thm_BooleanIsoperimetry_H_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n lo hi : ℕ) (hlohi : lo ≤ hi) :
    (∑ i ∈ Finset.Ico lo hi, HIncrement n i) = gShiftIntervalCount n lo hi := by
  have hwindow := H_window_sum_of_le n lo hi hlohi
  have hcount := gShiftIntervalCount_eq_H_sub n lo hi hlohi
  have hmono : H n lo ≤ H n hi := H_mono hlohi
  omega
end BooleanIsoperimetry
