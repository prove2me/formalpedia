-- Prove2me | solution 1 for BooleanIsoperimetry.gShift_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:32.163302+00:00
-- url     : https://prove2.me/submissions/e67288bd-2470-4650-ae9d-1d4c1879665b

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_card_gShift
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_gShift_mono

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} {w v : Cube n} (h : simplicialLe w v) :
    simplicialLe (gShift w) (gShift v) := by
  have hwv : w.card ≤ v.card := by rcases h with hlt | ⟨heq, _⟩ <;> omega
  have hgw := card_gShift w
  have hgv := card_gShift v
  by_cases hc : (gShift w).card < (gShift v).card
  · exact Or.inl hc
  · have hcardeq : (gShift w).card = (gShift v).card := by omega
    refine Or.inr ⟨hcardeq, ?_⟩
    by_cases hwc : w.card = v.card
    · rcases h with hlt | ⟨heq, hnat⟩
      · omega
      · exact cubeToNat_gShift_mono w.card w v rfl hwc.symm hnat
    · have hlt' : w.card < v.card := lt_of_le_of_ne hwv hwc
      have hw0 : (gShift w).card = 0 := by omega
      have hv0 : (gShift v).card = 0 := by omega
      rw [Finset.card_eq_zero] at hw0 hv0
      rw [hw0, hv0]
end BooleanIsoperimetry
