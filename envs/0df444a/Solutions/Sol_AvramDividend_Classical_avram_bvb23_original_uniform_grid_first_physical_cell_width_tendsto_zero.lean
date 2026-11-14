-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb23_original_uniform_grid_first_physical_cell_width_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:22.214445+00:00
-- url     : https://prove2.me/submissions/ebc23824-1bca-4766-9a0c-d7cc8092edd4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (T : ℝ) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    Tendsto (fun n : ℕ => (u n 1 : ℝ))
      atTop (𝓝 (0 : ℝ))  := by
  have h := (Filter.tendsto_add_atTop_iff_nat
    (f := fun k : ℕ => T / (k : ℝ))
    (l := 𝓝 (0 : ℝ)) 2).2
    (tendsto_const_div_atTop_nhds_zero_nat T)
  convert h using 1
  ext n
  rw [huniform n 1]
  push_cast
  ring
