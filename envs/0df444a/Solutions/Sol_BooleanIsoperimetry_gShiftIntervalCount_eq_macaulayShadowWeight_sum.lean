-- Prove2me | solution 1 for BooleanIsoperimetry.gShiftIntervalCount_eq_macaulayShadowWeight_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:21.91105+00:00
-- url     : https://prove2.me/submissions/73083082-b709-41a2-92d7-3be594527c02

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
public import Theorems.Thm_BooleanIsoperimetry_HIncrement_window_eq_macaulayShadowWeight_sum


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    (n lo hi : ℕ) (hlohi : lo ≤ hi) (hhi : hi ≤ 2 ^ n) :
    gShiftIntervalCount n lo hi =
      ∑ w ∈ (Finset.univ.filter (fun w : Cube n => lo ≤ rank w ∧ rank w < hi)),
        macaulayShadowWeight w := by
  rw [← HIncrement_window_eq_gShiftIntervalCount n lo hi hlohi]
  exact HIncrement_window_eq_macaulayShadowWeight_sum n lo hi hhi
end BooleanIsoperimetry
