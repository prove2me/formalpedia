-- Prove2me | solution 1 for BooleanIsoperimetry.gShiftIntervalCount_ge_binomPrefix_window_of_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:27.141089+00:00
-- url     : https://prove2.me/submissions/9679fe4f-e943-4736-83aa-95f0c6f99231

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
    (hlo : lo ≤ binomPrefix n r)
    (hhi : binomPrefix n s ≤ hi) :
    (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) ≤
      gShiftIntervalCount n lo hi := by
  have hle : lo ≤ hi := le_trans (le_trans hlo (binomPrefix_mono n hrs)) hhi
  rw [gShiftIntervalCount_eq_H_sub n lo hi hle]
  have h1 : H n lo ≤ H n (binomPrefix n r) := H_mono hlo
  have h2 : H n (binomPrefix n s) ≤ H n hi := H_mono hhi
  have h3 : H n (binomPrefix n s) - H n (binomPrefix n r) =
      (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) := by
    have h4 : binomPrefix n r ≤ binomPrefix n s := binomPrefix_mono n hrs
    rw [← gShiftIntervalCount_eq_H_sub n (binomPrefix n r) (binomPrefix n s) h4]
    exact gShiftIntervalCount_binomPrefix_window n r s hr hrs
  omega
end BooleanIsoperimetry
