-- Prove2me | solution 1 for BooleanIsoperimetry.gShiftIntervalCount_le_binomPrefix_window_of_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:26.763807+00:00
-- url     : https://prove2.me/submissions/a6c73c96-ce04-424e-8b5a-e00b87383071

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
public import Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_binomPrefix_window
public import Theorems.Thm_BooleanIsoperimetry_H_mono
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    (n r s lo hi : ℕ)
    (hr : 1 ≤ r) (hrs : r ≤ s)
    (hlo : binomPrefix n r ≤ lo)
    (hhi : hi ≤ binomPrefix n s) :
    gShiftIntervalCount n lo hi ≤
      (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) := by
  by_cases h : lo ≤ hi
  · rw [gShiftIntervalCount_eq_H_sub n lo hi h]
    have h1 : H n hi ≤ H n (binomPrefix n s) := H_mono hhi
    have h2 : H n (binomPrefix n r) ≤ H n lo := H_mono hlo
    have h3 : H n (binomPrefix n s) - H n (binomPrefix n r) =
        (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) := by
      have h4 : binomPrefix n r ≤ binomPrefix n s := binomPrefix_mono n hrs
      rw [← gShiftIntervalCount_eq_H_sub n (binomPrefix n r) (binomPrefix n s) h4]
      exact gShiftIntervalCount_binomPrefix_window n r s hr hrs
    omega
  · have h0 : gShiftIntervalCount n lo hi = 0 := by
      rw [gShiftIntervalCount]
      have h_empty : Finset.univ.filter
          (fun v : Cube n => lo ≤ rank (gShift v) ∧ rank (gShift v) < hi) = ∅ := by
        apply Finset.filter_false_of_mem
        intro v _
        omega
      rw [h_empty, Finset.card_empty]
    rw [h0]
    exact Nat.zero_le _
end BooleanIsoperimetry
