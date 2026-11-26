-- Prove2me | solution 1 for Erdos287.single_period_distance_packing
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T04:12:55.097087+00:00
-- url     : https://prove2.me/submissions/0a72f91f-b013-40fa-96b9-d419ee09e95c

import Mathlib

open Finset

set_option autoImplicit false

/-- At most `u` locations in one interval of length `u + v` avoid distances in `[u, v]`. -/
theorem solution (u v : ℕ) (S : Finset ℕ) (hu : 0 < u) (hv : 2 * u ≤ v + 2)
    (hS : ∀ s ∈ S, s < u + v)
    (havoid : ∀ x ∈ S, ∀ y ∈ S, u ≤ y - x → v < y - x) : S.card ≤ u := by
  classical
  rcases eq_empty_or_nonempty S with rfl | hne
  · simp
  let a := S.min' hne
  let B := S.filter (fun s => s < a + u)
  have ha : a ∈ S := S.min'_mem hne
  have hB : B.Nonempty := ⟨a, mem_filter.mpr ⟨ha, by omega⟩⟩
  let b := B.max' hB
  have hb : b ∈ B := B.max'_mem hB
  have hbS := (mem_filter.mp hb).1
  have hbsmall := (mem_filter.mp hb).2
  let R := S \ B
  have hdisj : Disjoint R B := disjoint_left.mpr (fun s hs hsb => (mem_sdiff.mp hs).2 hsb)
  have hsplit : R.card + B.card = S.card := by
    rw [← card_union_of_disjoint hdisj, sdiff_union_of_subset (filter_subset _ _)]
  have hBcard : B.card ≤ b + 1 - a := by
    have hsub : B ⊆ Icc a b := fun s hs =>
      mem_Icc.mpr ⟨S.min'_le _ (mem_filter.mp hs).1, B.le_max' _ hs⟩
    simpa using card_le_card hsub
  have hab : a ≤ b := S.min'_le _ hbS
  rcases eq_empty_or_nonempty R with hR | hR
  · simp only [hR, card_empty, zero_add] at hsplit
    omega
  have hsub : R ⊆ Ico (b + v + 1) (u + v) := by
    intro r hr
    obtain ⟨hrS, hrB⟩ := mem_sdiff.mp hr
    have hlarge : a + u ≤ r := by
      by_contra! hlt
      exact hrB (mem_filter.mpr ⟨hrS, hlt⟩)
    have hfar := havoid a ha r hrS (by omega)
    have hfar' := havoid b hbS r hrS (by omega)
    exact mem_Ico.mpr ⟨by omega, hS r hrS⟩
  have hRcard : R.card ≤ (u + v) - (b + v + 1) := by
    simpa using card_le_card hsub
  obtain ⟨r, hr⟩ := hR
  have hbr := mem_Ico.mp (hsub hr)
  omega

