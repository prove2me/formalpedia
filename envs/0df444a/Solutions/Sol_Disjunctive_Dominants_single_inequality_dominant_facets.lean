-- Prove2me | solution 1 for Disjunctive.Dominants.single_inequality_dominant_facets
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:42:29.337387+00:00
-- url     : https://prove2.me/submissions/1b3fbbd6-8ddc-42f1-a526-10f074178ed2

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

open Disjunctive.Dominants in
theorem solution {n : ℕ} (a : Fin n → ℝ) (ha : 0 ≤ a)
    (P : Set (Fin n → ℝ)) (hP : P = UnitCube n ∩ {x | 1 ≤ dotProduct a x})
    (hupper : IsUpperMonotone P) (haN : 1 ≤ ∑ j, a j) :
    Dominant P = {x | 0 ≤ x ∧ ∀ S : Finset (Fin n), 0 < 1 - SumOver a (Finset.univ \ S) →
      1 ≤ (∑ j ∈ S, a j * x j) / (1 - SumOver a (Finset.univ \ S))} := by
  subst hP
  ext x
  simp only [Dominant, Set.mem_ofPred_eq, Set.mem_inter_iff, UnitCube, SumOver]
  constructor
  · rintro ⟨hx0, y, ⟨hy01, hya⟩, hyx⟩
    refine ⟨hx0, fun S hS => ?_⟩
    rw [← Finset.compl_eq_univ_sdiff] at hS ⊢
    rw [le_div_iff₀ hS, one_mul]
    have hsplit : dotProduct a y = ∑ j ∈ S, a j * y j + ∑ j ∈ Sᶜ, a j * y j := by
      rw [dotProduct, Finset.sum_add_sum_compl]
    have h1 : ∑ j ∈ S, a j * y j ≤ ∑ j ∈ S, a j * x j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hyx j) (ha j)
    have h2 : ∑ j ∈ Sᶜ, a j * y j ≤ ∑ j ∈ Sᶜ, a j :=
      Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (ha j) (hy01 j).2
    linarith
  · rintro ⟨hx0, hS⟩
    refine ⟨hx0, fun j => min (x j) 1,
      ⟨fun j => ⟨le_min (hx0 j) zero_le_one, min_le_right _ _⟩, ?_⟩, fun j => min_le_left _ _⟩
    set S := Finset.univ.filter (fun j => x j < 1) with hSdef
    have hsplit : dotProduct a (fun j => min (x j) 1)
        = ∑ j ∈ S, a j * x j + ∑ j ∈ Sᶜ, a j := by
      rw [dotProduct, ← Finset.sum_add_sum_compl S]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : x j < 1 := by simpa [hSdef] using hj
        rw [min_eq_left hj'.le]
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : 1 ≤ x j := by simpa [hSdef] using hj
        rw [min_eq_right hj', mul_one]
    rw [hsplit]
    have hSnn : 0 ≤ ∑ j ∈ S, a j * x j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (hx0 j)
    by_cases hd : 0 < 1 - ∑ j ∈ Sᶜ, a j
    · have h := hS S (by rw [← Finset.compl_eq_univ_sdiff]; exact hd)
      rw [← Finset.compl_eq_univ_sdiff, le_div_iff₀ hd, one_mul] at h
      linarith
    · linarith
