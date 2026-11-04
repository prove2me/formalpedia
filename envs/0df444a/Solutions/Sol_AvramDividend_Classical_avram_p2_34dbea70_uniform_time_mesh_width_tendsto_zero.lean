-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:27:23.346704+00:00
-- url     : https://prove2.me/submissions/76cc4fcb-8e20-4956-8450-330b7d3056c7

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

/-- Uniform right-closed grid cells have width tending to zero. -/
theorem solution (T : ℝ≥0) :
    Tendsto (fun n : ℕ => T / ((n : ℝ≥0) + 1)) atTop
      (𝓝 (0 : ℝ≥0)) := by
  have hbase : Tendsto
      (fun n : ℕ => (1 : ℝ≥0) / ((n : ℝ≥0) + 1)) atTop
      (𝓝 (0 : ℝ≥0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmul : Tendsto
      (fun n : ℕ => T * ((1 : ℝ≥0) / ((n : ℝ≥0) + 1))) atTop
      (𝓝 (0 : ℝ≥0)) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hbase)
  simpa [div_eq_mul_inv] using hmul
