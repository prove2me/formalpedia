-- Prove2me | solution 1 for BooleanIsoperimetry.gShiftIntervalCount_le_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:40.265193+00:00
-- url     : https://prove2.me/submissions/0f346955-c806-4135-b2cf-394900790e33

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
public import Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_le_binomPrefix_window_of_endpoints
public import Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_ge_binomPrefix_window_of_endpoints

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    (n r₁ s₁ r₂ s₂ lo₁ hi₁ lo₂ hi₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hrs₁ : r₁ ≤ s₁)
    (hr₂ : 1 ≤ r₂) (hrs₂ : r₂ ≤ s₂)
    (hlo₁ : binomPrefix n r₁ ≤ lo₁) (hhi₁ : hi₁ ≤ binomPrefix n s₁)
    (hlo₂ : lo₂ ≤ binomPrefix n r₂) (hhi₂ : binomPrefix n s₂ ≤ hi₂)
    (hblock :
      (Finset.Ico (r₁ + 1) (s₁ + 1)).sum (fun i => Nat.choose n i) ≤
        (Finset.Ico (r₂ + 1) (s₂ + 1)).sum (fun i => Nat.choose n i)) :
    gShiftIntervalCount n lo₁ hi₁ ≤ gShiftIntervalCount n lo₂ hi₂ := by
  have hup :=
    gShiftIntervalCount_le_binomPrefix_window_of_endpoints n r₁ s₁ lo₁ hi₁ hr₁ hrs₁ hlo₁ hhi₁
  have hlow :=
    gShiftIntervalCount_ge_binomPrefix_window_of_endpoints n r₂ s₂ lo₂ hi₂ hr₂ hrs₂ hlo₂ hhi₂
  omega
end BooleanIsoperimetry
