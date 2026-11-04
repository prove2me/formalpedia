-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:28:13.443141+00:00
-- url     : https://prove2.me/submissions/607f9b88-5832-4f4b-80eb-e957c71dd17c

import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_increment_to_jump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

/-- The original nonnegative uniform grid width T/(n+1) vanishes. -/
theorem solution (T : ℝ≥0) :
    Tendsto (fun n : ℕ => T / ((n : ℝ≥0) + 1))
      atTop (𝓝 (0 : ℝ≥0)) := by
  have hbase : Tendsto (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hreal : Tendsto (fun n : ℕ =>
      (T : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_zero] using
      hbase.const_mul (T : ℝ)
  apply (NNReal.tendsto_coe).mp
  convert hreal using 1 <;> norm_num
