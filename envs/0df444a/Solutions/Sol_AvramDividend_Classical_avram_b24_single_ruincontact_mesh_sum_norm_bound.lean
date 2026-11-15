-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_single_ruincontact_mesh_sum_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:26:51.692805+00:00
-- url     : https://prove2.me/submissions/74f8f9db-a399-41db-b61b-c0a6c163d2de

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
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hV : ∀ i ∈ S, ‖V i‖ ≤ ε) :
    ‖∑ i ∈ S.filter (fun i => a i < σ ∧ σ ≤ b i), V i‖ ≤ ε := by
  classical
  let C := S.filter (fun i => a i < σ ∧ σ ≤ b i)
  have unique (i j : ℕ) (hi : i ∈ C) (hj : j ∈ C) : i = j := by
    obtain ⟨hiS, hiC⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjS, hjC⟩ := Finset.mem_filter.mp hj
    exact avram_b24_unique_ruincontact_cell_on_separated_grid
      S a b hSep σ i hiS j hjS hiC.1 hiC.2 hjC.1 hjC.2
  by_cases hEmpty : C = ∅
  · change ‖∑ i ∈ C, V i‖ ≤ ε
    rw [hEmpty]
    simpa using hε
  · have hNonempty : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨i, hi⟩ := hNonempty
    have hSingle : C = {i} := by
      ext j
      constructor
      · intro hj
        exact Finset.mem_singleton.mpr (unique j i hj hi)
      · intro hj
        have eq : j = i := Finset.mem_singleton.mp hj
        simpa [eq] using hi
    change ‖∑ j ∈ C, V j‖ ≤ ε
    rw [hSingle]
    simpa only [Finset.sum_singleton] using
      hV i (Finset.mem_filter.mp hi).1
