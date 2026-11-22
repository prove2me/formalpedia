-- Prove2me | solution 1 for BooleanIsoperimetry.gShiftIntervalCount_binomPrefix_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:28.93899+00:00
-- url     : https://prove2.me/submissions/398f177f-90aa-43fb-aac0-9b039fea0743

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
public import Theorems.Thm_BooleanIsoperimetry_H_binomPrefix_window
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) :
    gShiftIntervalCount n (binomPrefix n r) (binomPrefix n s)
      = (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) := by
  have hle : binomPrefix n r ≤ binomPrefix n s := binomPrefix_mono n hrs
  rw [gShiftIntervalCount_eq_H_sub n _ _ hle]
  have hw := H_binomPrefix_window n r s hr hrs
  omega
end BooleanIsoperimetry
