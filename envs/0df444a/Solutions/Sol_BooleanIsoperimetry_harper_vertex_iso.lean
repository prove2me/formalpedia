-- Prove2me | solution 1 for BooleanIsoperimetry.harper_vertex_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:50:47.090793+00:00
-- url     : https://prove2.me/submissions/abc1db07-ff92-4501-99ce-00cf729f45c0

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Theorems.Thm_BooleanIsoperimetry_harper_split_min
public import Theorems.Thm_BooleanIsoperimetry_H_full
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_succ
public import Theorems.Thm_BooleanIsoperimetry_slice_card_add
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N : ℕ) (A : Finset (Cube N)) :
    H N A.card ≤ (neighborhood 1 A).card := by
  induction N with
  | zero =>
    have hle : A.card ≤ 1 := by
      have := Finset.card_le_univ A
      simpa [Cube, Fintype.card_finset, Fintype.card_fin] using this
    have hsub : A ⊆ neighborhood 1 A := fun x hx => by
      rw [mem_neighborhood_iff]; exact ⟨x, hx, by simp [hDist]⟩
    have hAcard : A.card ≤ (neighborhood 1 A).card := Finset.card_le_card hsub
    rcases Nat.lt_or_ge A.card 1 with h | h
    · have h0 : A.card = 0 := by omega
      rw [h0, H_zero]; exact Nat.zero_le _
    · have h1 : A.card = 1 := by omega
      have hH : H 0 1 = 1 := by simpa using H_full 0
      rw [h1, hH]
      rw [h1] at hAcard
      exact hAcard
  | succ n ih =>
    set a0 := (slice0 A).card with ha0
    set a1 := (slice1 A).card with ha1
    have hcap0 : a0 ≤ 2 ^ n := by
      have := Finset.card_le_univ (slice0 A)
      simpa [Cube, Fintype.card_finset, Fintype.card_fin] using this
    have hcap1 : a1 ≤ 2 ^ n := by
      have := Finset.card_le_univ (slice1 A)
      simpa [Cube, Fintype.card_finset, Fintype.card_fin] using this
    have hAcard : A.card = a0 + a1 := by rw [ha0, ha1, slice_card_add]
    have hIH0 := ih (slice0 A)
    have hIH1 := ih (slice1 A)
    have hterm1 : max (H n a0) a1 ≤ (neighborhood 1 (slice0 A) ∪ slice1 A).card := by
      apply max_le
      · exact le_trans hIH0 (Finset.card_le_card Finset.subset_union_left)
      · rw [ha1]; exact Finset.card_le_card Finset.subset_union_right
    have hterm2 : max (H n a1) a0 ≤ (neighborhood 1 (slice1 A) ∪ slice0 A).card := by
      apply max_le
      · exact le_trans hIH1 (Finset.card_le_card Finset.subset_union_left)
      · rw [ha0]; exact Finset.card_le_card Finset.subset_union_right
    have hsum : max (H n a0) a1 + max (H n a1) a0 ≤ (neighborhood 1 A).card := by
      rw [neighborhood_succ]; exact Nat.add_le_add hterm1 hterm2
    have hsplit := harper_split_min (n := n) hcap0 hcap1
    rw [hAcard]
    exact le_trans hsplit hsum
end BooleanIsoperimetry
