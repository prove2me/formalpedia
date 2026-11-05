-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_rate_limit_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:00:05.026674+00:00
-- url     : https://prove2.me/submissions/185d60f6-d868-4c7e-858f-6cc01690caaa

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-- Triangular equal-cell original marked-count rate factors converge to one half. -/
theorem solution (T rate : ℝ) :
    Tendsto
      (fun k : ℕ => ((T * rate) ^ 2 / 2) *
        ((k : ℝ) / ((k : ℝ) + 1))) atTop
      (𝓝 ((T * rate) ^ 2 / 2)) := by
  have hrecip :
      Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio :
      Tendsto (fun k : ℕ => (1 : ℝ) - 1 / ((k : ℝ) + 1))
        atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub hrecip using 1 <;> norm_num
  have hprod :
      Tendsto (fun k : ℕ => ((T * rate) ^ 2 / 2) *
        ((1 : ℝ) - 1 / ((k : ℝ) + 1)))
        atTop (𝓝 ((T * rate) ^ 2 / 2)) := by
    simpa using (tendsto_const_nhds.mul hratio)
  apply hprod.congr'
  filter_upwards [] with k
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hk]
  ring
