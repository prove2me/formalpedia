-- Prove2me | solution 1 for BooleanIsoperimetry.gShiftIntervalCount_le_of_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:40.950991+00:00
-- url     : https://prove2.me/submissions/49310730-8c79-4aa8-b7b2-e6fdeeb5c6b0

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
public import Theorems.Thm_BooleanIsoperimetry_HIncrement_window_le_of_layer


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n r a L : ℕ} (hr : 1 ≤ r)
    (hlo : binomPrefix n r ≤ a) (hhi : a + L ≤ binomPrefix n (r + 1)) :
    gShiftIntervalCount n a (a + L) ≤ L * (n - r) := by
  rw [← HIncrement_window_eq_gShiftIntervalCount n a (a + L) (by omega)]
  exact HIncrement_window_le_of_layer hr hlo hhi
end BooleanIsoperimetry
