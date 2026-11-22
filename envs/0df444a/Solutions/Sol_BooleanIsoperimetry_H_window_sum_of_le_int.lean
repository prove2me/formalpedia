-- Prove2me | solution 1 for BooleanIsoperimetry.H_window_sum_of_le_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:22.845797+00:00
-- url     : https://prove2.me/submissions/fd09bc73-4967-4f5e-9bec-4ebed633e0ab

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
public import Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_eq_H_sub
public import Theorems.Thm_BooleanIsoperimetry_H_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n lo hi : ℕ) (hlohi : lo ≤ hi) :
    (H n hi : ℤ) = (H n lo : ℤ) + (gShiftIntervalCount n lo hi : ℤ) := by
  rw [gShiftIntervalCount_eq_H_sub n lo hi hlohi]
  have Hmono : H n lo ≤ H n hi := H_mono hlohi
  omega
end BooleanIsoperimetry
