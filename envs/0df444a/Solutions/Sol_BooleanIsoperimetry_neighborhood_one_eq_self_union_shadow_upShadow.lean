-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_one_eq_self_union_shadow_upShadow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:47.246123+00:00
-- url     : https://prove2.me/submissions/718a5d72-8a7d-4b9b-bead-ffe9f24c6635

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A : Finset (Cube N)) :
    neighborhood 1 A = A ∪ Finset.shadow A ∪ Finset.upShadow A := by
  ext v
  simp only [Finset.mem_union, mem_neighborhood_iff]
  constructor
  · rintro ⟨u, huA, hd⟩
    have hsplit : symmDiff u v = (u \ v) ∪ (v \ u) := by
      ext y; simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
    have hdisj : Disjoint (u \ v) (v \ u) := disjoint_sdiff_sdiff
    have hcard : (u \ v).card + (v \ u).card ≤ 1 := by
      have : (symmDiff u v).card ≤ 1 := hd
      rwa [hsplit, Finset.card_union_of_disjoint hdisj] at this
    rcases Nat.eq_zero_or_pos (u \ v).card with huv0 | huvpos
    · rcases Nat.eq_zero_or_pos (v \ u).card with hvu0 | hvupos
      · have hsub1 : u ⊆ v := by
          rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]; exact huv0
        have hsub2 : v ⊆ u := by
          rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]; exact hvu0
        have huv : u = v := Finset.Subset.antisymm hsub1 hsub2
        exact Or.inl (Or.inl (huv ▸ huA))
      · have hvu1 : (v \ u).card = 1 := by omega
        have hsub : u ⊆ v := by
          rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]; exact huv0
        refine Or.inr ?_
        rw [Finset.mem_upShadow_iff_exists_sdiff]
        exact ⟨u, huA, hsub, hvu1⟩
    · have huv1 : (u \ v).card = 1 := by omega
      have hvu0 : (v \ u).card = 0 := by omega
      have hsub : v ⊆ u := by
        rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]; exact hvu0
      refine Or.inl (Or.inr ?_)
      rw [Finset.mem_shadow_iff_exists_sdiff]
      exact ⟨u, huA, hsub, huv1⟩
  · rintro ((hv | hv) | hv)
    · exact ⟨v, hv, by simp [hDist]⟩
    · rw [Finset.mem_shadow_iff_exists_sdiff] at hv
      obtain ⟨s, hs, hvs, hcard⟩ := hv
      refine ⟨s, hs, ?_⟩
      have hss : symmDiff s v = s \ v := by
        ext y
        simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
        constructor
        · rintro (⟨hys, hyv⟩ | ⟨hyv, hys⟩)
          · exact ⟨hys, hyv⟩
          · exact absurd (hvs hyv) hys
        · rintro ⟨hys, hyv⟩; exact Or.inl ⟨hys, hyv⟩
      have : hDist s v = 1 := by unfold hDist; rw [hss]; exact hcard
      omega
    · rw [Finset.mem_upShadow_iff_exists_sdiff] at hv
      obtain ⟨s, hs, hsv, hcard⟩ := hv
      refine ⟨s, hs, ?_⟩
      have hss : symmDiff s v = v \ s := by
        ext y
        simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
        constructor
        · rintro (⟨hys, hyv⟩ | ⟨hyv, hys⟩)
          · exact absurd (hsv hys) hyv
          · exact ⟨hyv, hys⟩
        · rintro ⟨hyv, hys⟩; exact Or.inr ⟨hyv, hys⟩
      have : hDist s v = 1 := by unfold hDist; rw [hss]; exact hcard
      omega
end BooleanIsoperimetry
