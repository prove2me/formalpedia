-- Prove2me | solution 1 for Erdos287.odd_positions_meet_quotas_outside_blocked_layers
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:33:21.084015+00:00
-- url     : https://prove2.me/submissions/3d3684f9-ac08-4fd2-a994-d4313b431dba

import Mathlib

open Finset

set_option autoImplicit false

/-- Odd candidate positions away from the certified holes can be omitted
together. Few layer quotas fail when the total blocked occupancy is small. -/
theorem solution (H U P : Finset ℕ) (label : ℕ → ℕ) (R S : ℕ)
    (hH : ∀ n ∈ H, n + 1 ∉ H) (hU : ∀ n ∈ U, Odd n)
    (hsize : ∀ p ∈ P, R + S ≤ (U.filter (fun n => label n = p)).card) :
    let B := U.filter (fun n => n ∈ H ∨ n - 1 ∈ H ∨ n + 1 ∈ H)
    let A := U \ B
    let X := H ∪ A
    (∀ n ∈ X, n + 1 ∉ X) ∧
      (P.filter (fun p => (A.filter (fun n => label n = p)).card < R)).card * S ≤ B.card := by
  classical
  intro B A X
  have hA (n : ℕ) (hn : n ∈ A) : n ∈ U ∧ n ∉ H ∧ n - 1 ∉ H ∧ n + 1 ∉ H := by
    obtain ⟨hnU, hnB⟩ := mem_sdiff.mp hn
    exact ⟨hnU, fun h => hnB (mem_filter.mpr ⟨hnU, Or.inl h⟩),
      fun h => hnB (mem_filter.mpr ⟨hnU, Or.inr (Or.inl h)⟩),
      fun h => hnB (mem_filter.mpr ⟨hnU, Or.inr (Or.inr h)⟩)⟩
  constructor
  · intro n hn hs
    rcases mem_union.mp hn with hnH | hnA <;> rcases mem_union.mp hs with hsH | hsA
    · exact hH n hnH hsH
    · exact (hA _ hsA).2.2.1 (by simpa using hnH)
    · exact (hA _ hnA).2.2.2 hsH
    · obtain ⟨i, hi⟩ := hU n (hA n hnA).1
      obtain ⟨j, hj⟩ := hU (n + 1) (hA _ hsA).1
      omega
  · let Bad := P.filter (fun p => (A.filter (fun n => label n = p)).card < R)
    let F (p : ℕ) := B.filter (fun n => label n = p)
    have hF (p : ℕ) (hp : p ∈ Bad) : S ≤ (F p).card := by
      obtain ⟨hpP, hpR⟩ := mem_filter.mp hp
      let Uₚ := U.filter (fun n => label n = p)
      have hsub : F p ⊆ Uₚ := by
        intro n hn
        obtain ⟨hnB, hnL⟩ := mem_filter.mp hn
        exact mem_filter.mpr ⟨(mem_filter.mp hnB).1, hnL⟩
      have hdiff : Uₚ \ F p = A.filter (fun n => label n = p) := by
        ext n
        by_cases hn : label n = p <;> simp [Uₚ, F, A, hn]
      have hCount := card_sdiff_add_card_eq_card hsub
      rw [hdiff] at hCount
      have hUcard : R + S ≤ Uₚ.card := hsize p hpP
      omega
    have hpair : (↑Bad : Set ℕ).PairwiseDisjoint F := by
      intro p hp q hq hpq
      exact disjoint_left.mpr fun n hn hn' =>
        hpq ((mem_filter.mp hn).2.symm.trans (mem_filter.mp hn').2)
    have hcover : Bad.biUnion F ⊆ B := by
      intro n hn
      obtain ⟨p, hp, hn⟩ := mem_biUnion.mp hn
      exact (mem_filter.mp hn).1
    calc
      Bad.card * S = ∑ _ ∈ Bad, S := by simp
      _ ≤ ∑ p ∈ Bad, (F p).card := sum_le_sum hF
      _ = (Bad.biUnion F).card := (card_biUnion hpair).symm
      _ ≤ B.card := card_le_card hcover

