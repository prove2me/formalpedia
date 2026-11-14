-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB287_positive_mesh_open_cells_or_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:06:35.880647+00:00
-- url     : https://prove2.me/submissions/8245de5c-8a44-422f-92b7-329ff9fa3931

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB282_positive_finite_time_grid_half_open_cell_cover
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
noncomputable section

/-- Every time before a positive finite-grid horizon is inside an open cell or on a finite boundary. -/
theorem solution (N : ℕ) (δ t : ℝ)
    (hδ : 0 < δ) (ht : 0 ≤ t) (horizon : t < (N : ℝ) * δ) :
    (∃ i : ℕ, i < N ∧
      t ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ)) ∨
    t ∈ Set.range (fun i : Fin N => (i : ℝ) * δ) := by
  obtain ⟨i, hi, hlow, hupp⟩ :=
    avram_gbB282_positive_finite_time_grid_half_open_cell_cover
      N δ t hδ ht horizon
  by_cases heq : t = (i : ℝ) * δ
  · right
    exact ⟨⟨i, hi⟩, by simpa using heq.symm⟩
  · left
    refine ⟨i, hi, ?_⟩
    exact ⟨lt_of_le_of_ne hlow (Ne.symm heq), hupp⟩
