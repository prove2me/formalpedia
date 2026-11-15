-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_ruinclipped_mesh_interior_contact_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:59:31.168595+00:00
-- url     : https://prove2.me/submissions/febafa28-d8ec-4d5d-ba7a-20358f6340c4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_unique_ruincontact_cell_on_separated_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (σ : ℝ≥0)
    (H : ℕ → ℝ)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j) :
    (∑ i ∈ S, if σ ≤ a i then 0 else H i) =
        (∑ i ∈ S.filter (fun i => b i < σ), H i) +
        (∑ i ∈ S.filter (fun i => a i < σ ∧ σ ≤ b i), H i) ∧
    (∀ i ∈ S.filter (fun i => a i < σ ∧ σ ≤ b i),
     ∀ j ∈ S.filter (fun j => a j < σ ∧ σ ≤ b j), i = j) := by
  classical
  constructor
  · simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hBefore : σ ≤ a i
    · have hNotA : ¬ a i < σ := not_lt.mpr hBefore
      have hNotB : ¬ b i < σ := not_lt.mpr (le_trans hBefore (hab i hi))
      simp [hBefore, hNotA, hNotB]
    · have hAfter : a i < σ := lt_of_not_ge hBefore
      by_cases hInside : b i < σ
      · have hNotContact : ¬ σ ≤ b i := not_le.mpr hInside
        simp [hBefore, hAfter, hInside, hNotContact]
      · have hContact : σ ≤ b i := le_of_not_gt hInside
        simp [hBefore, hAfter, hInside, hContact]
  · intro i hi j hj
    obtain ⟨hiS, hiC⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjS, hjC⟩ := Finset.mem_filter.mp hj
    exact avram_b24_unique_ruincontact_cell_on_separated_grid
      S a b hSep σ i hiS j hjS hiC.1 hiC.2 hjC.1 hjC.2
