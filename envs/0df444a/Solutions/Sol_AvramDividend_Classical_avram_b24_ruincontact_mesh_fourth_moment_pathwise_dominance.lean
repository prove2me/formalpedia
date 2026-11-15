-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_ruincontact_mesh_fourth_moment_pathwise_dominance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:31:51.036321+00:00
-- url     : https://prove2.me/submissions/972935c0-af29-4d8f-89ce-49c5ff31a24b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_unique_ruincontact_cell_on_separated_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (σ : ℝ≥0) (V : ℕ → ℝ)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j) :
    (‖∑ i ∈ S.filter (fun i => a i < σ ∧ σ ≤ b i), V i‖)^4 ≤
      ∑ i ∈ S, (‖V i‖)^4 := by
  classical
  let C := S.filter (fun i => a i < σ ∧ σ ≤ b i)
  have unique (i j : ℕ) (hi : i ∈ C) (hj : j ∈ C) : i = j := by
    obtain ⟨hiS, hiC⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjS, hjC⟩ := Finset.mem_filter.mp hj
    exact avram_b24_unique_ruincontact_cell_on_separated_grid
      S a b hSep σ i hiS j hjS hiC.1 hiC.2 hjC.1 hjC.2
  by_cases hEmpty : C = ∅
  · change ‖∑ i ∈ C, V i‖ ^ 4 ≤ ∑ i ∈ S, ‖V i‖ ^ 4
    rw [hEmpty]
    simpa using (Finset.sum_nonneg (s := S)
      (f := fun i => (‖V i‖)^4)
      (fun i _ => pow_nonneg (norm_nonneg (V i)) _))
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hSingle : C = {i} := by
      ext j
      constructor
      · intro hj
        exact Finset.mem_singleton.mpr (unique j i hj hi)
      · intro hj
        simpa [Finset.mem_singleton.mp hj] using hi
    change ‖∑ j ∈ C, V j‖ ^ 4 ≤ ∑ j ∈ S, ‖V j‖ ^ 4
    rw [hSingle, Finset.sum_singleton]
    exact Finset.single_le_sum
      (fun j _ => pow_nonneg (norm_nonneg (V j)) _)
      (Finset.mem_filter.mp hi).1
