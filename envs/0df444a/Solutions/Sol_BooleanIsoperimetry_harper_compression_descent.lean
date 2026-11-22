-- Prove2me | solution 1 for BooleanIsoperimetry.harper_compression_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:52:49.856261+00:00
-- url     : https://prove2.me/submissions/dca56d77-e10f-41f8-b7ae-96cae8dbbe5c

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_MacaulayMin
public import Theorems.Thm_BooleanIsoperimetry_harper_macaulay_min
public import Theorems.Thm_BooleanIsoperimetry_H_one
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_card_le_two_pow
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_succ
public import Theorems.Thm_BooleanIsoperimetry_slice_card_add
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A : Finset (Cube N)) :
    (neighborhood 1 (simplicialInitSeg N A.card)).card ≤ (neighborhood 1 A).card := by
  suffices h : ∀ (M : ℕ) (B : Finset (Cube M)), H M B.card ≤ (neighborhood 1 B).card by
    exact h N A
  intro M
  induction M with
  | zero =>
    intro B
    have hsub : B ⊆ neighborhood 1 B := by
      intro x hx
      rw [mem_neighborhood_iff]
      exact ⟨x, hx, by simp [hDist]⟩
    have hge : B.card ≤ (neighborhood 1 B).card := Finset.card_le_card hsub
    have hcard : B.card ≤ 1 := by
      have h := card_le_two_pow B; simpa using h
    rcases (by omega : B.card = 0 ∨ B.card = 1) with h0 | h1
    · rw [h0, H_zero]; exact Nat.zero_le _
    · rw [h1, H_one]; omega
  | succ M ih =>
    intro B
    set a := (slice0 B).card with ha_def
    set b := (slice1 B).card with hb_def
    have hab : a + b = B.card := slice_card_add B
    have ha : a ≤ 2 ^ M := card_le_two_pow (slice0 B)
    have hb : b ≤ 2 ^ M := card_le_two_pow (slice1 B)
    have ih0 : H M a ≤ (neighborhood 1 (slice0 B)).card := ih (slice0 B)
    have ih1 : H M b ≤ (neighborhood 1 (slice1 B)).card := ih (slice1 B)
    have bound1 : max (H M a) b ≤ (neighborhood 1 (slice0 B) ∪ slice1 B).card := by
      apply max_le
      · exact le_trans ih0 (Finset.card_le_card Finset.subset_union_left)
      · exact le_trans (le_of_eq hb_def) (Finset.card_le_card Finset.subset_union_right)
    have bound2 : max (H M b) a ≤ (neighborhood 1 (slice1 B) ∪ slice0 B).card := by
      apply max_le
      · exact le_trans ih1 (Finset.card_le_card Finset.subset_union_left)
      · exact le_trans (le_of_eq ha_def) (Finset.card_le_card Finset.subset_union_right)
    have hnb : (neighborhood 1 B).card =
        (neighborhood 1 (slice0 B) ∪ slice1 B).card +
        (neighborhood 1 (slice1 B) ∪ slice0 B).card := neighborhood_succ B
    have hleaf : H (M + 1) (a + b) ≤ max (H M a) b + max (H M b) a :=
      harper_macaulay_min ha hb
    rw [← hab]
    calc H (M + 1) (a + b)
        ≤ max (H M a) b + max (H M b) a := hleaf
      _ ≤ (neighborhood 1 (slice0 B) ∪ slice1 B).card +
            (neighborhood 1 (slice1 B) ∪ slice0 B).card := Nat.add_le_add bound1 bound2
      _ = (neighborhood 1 B).card := hnb.symm
end BooleanIsoperimetry
