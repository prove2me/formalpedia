-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB105_original_uniform_floor_left_endpoint_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:40:39.764357+00:00
-- url     : https://prove2.me/submissions/440adcd4-ea98-4422-a580-c9ff2943b13f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB103_uniform_mesh_left_approximation_squeeze
import Theorems.Thm_AvramDividend_Classical_avram_gbB104_uniform_floor_cell_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun m : ℕ =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
      ((⌊t / Δ⌋₊ : ℕ) : ℝ) * Δ)
      atTop (𝓝 t) := by
  apply avram_gbB103_uniform_mesh_left_approximation_squeeze n hn t
  · intro m
    exact (avram_gbB104_uniform_floor_cell_gap n m hn t ht).1
  · intro m
    exact (avram_gbB104_uniform_floor_cell_gap n m hn t ht).2
