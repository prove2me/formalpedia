-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_contact_left_endpoint_real_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:51:32.65644+00:00
-- url     : https://prove2.me/submissions/e0d49b62-8a61-482e-b061-16c57b9b2897

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal

/-- The physical contact-tail left endpoint approaches the actual stopped clock. -/
theorem solution
    (τ T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      ((τ - T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ))
      atTop (𝓝 (τ : ℝ)) := by
  have hwidth : Tendsto (fun n : ℕ =>
      T / ((n : ℝ≥0) + 1)) atTop (𝓝 (0 : ℝ≥0)) :=
    avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero T
  have hwidthReal : Tendsto (fun n : ℕ =>
      ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
    (NNReal.tendsto_coe).mpr hwidth
  have hdiff : Tendsto (fun n : ℕ =>
      (τ : ℝ) - ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ))
      atTop (𝓝 ((τ : ℝ) - 0)) :=
    tendsto_const_nhds.sub hwidthReal
  have hmax : Tendsto (fun n : ℕ =>
      max ((τ : ℝ) - ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ)) 0)
      atTop (𝓝 (max ((τ : ℝ) - 0) 0)) :=
    hdiff.max tendsto_const_nhds
  simpa only [NNReal.coe_sub_def, sub_zero,
    max_eq_left (NNReal.coe_nonneg τ)] using hmax
