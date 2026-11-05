-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_uniform_grid_quadratic_rate_tendsto_half_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:56:59.791794+00:00
-- url     : https://prove2.me/submissions/a3777170-6e38-413c-a6fd-8a4bb9d383c8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
noncomputable section

/-- The deterministic chronological cross-grid coefficient tends to one half. -/
theorem solution :
    Filter.Tendsto (fun m : ℕ =>
      (((2 : ℝ) ^ m - 1) / (2 * (2 : ℝ) ^ m)))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hsmall : Filter.Tendsto
      (fun m : ℕ => (1 / 2 : ℝ) ^ m)
      Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hprod : Filter.Tendsto
      (fun m : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m)
      Filter.atTop (nhds (0 : ℝ)) := by
    have h : Filter.Tendsto
        (fun m : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds ((1 / 2 : ℝ) * 0)) :=
      tendsto_const_nhds.mul hsmall
    simpa only [mul_zero] using h
  have hlim : Filter.Tendsto
      (fun m : ℕ => (1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m)
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
    have h : Filter.Tendsto
        (fun m : ℕ => (1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds ((1 / 2 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hprod
    simpa only [sub_zero] using h
  have hident (m : ℕ) :
      (((2 : ℝ) ^ m - 1) / (2 * (2 : ℝ) ^ m)) =
        (1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m := by
    have hn : (2 : ℝ) ^ m ≠ 0 := by positivity
    have he : (1 / 2 : ℝ) ^ m = 1 / (2 : ℝ) ^ m := by
      rw [div_pow]
      norm_num
    rw [he]
    field_simp [hn]
  simpa only [hident] using hlim
