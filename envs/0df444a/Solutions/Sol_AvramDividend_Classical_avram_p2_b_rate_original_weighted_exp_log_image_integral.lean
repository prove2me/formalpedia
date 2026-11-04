-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_weighted_exp_log_image_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:54:39.85949+00:00
-- url     : https://prove2.me/submissions/702633e1-607d-4d1a-beb4-69f0fc88ce65

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (ρ θ : ℝ) :
    (∫ z : ℝ, Real.exp (ρ * Real.log z) *
      (Real.exp (θ * Real.log z) - 1) ^ 4
      ∂(μ.map (fun ω => Real.exp (Y ω)))) =
    ∫ ω, Real.exp (ρ * Y ω) *
      (Real.exp (θ * Y ω) - 1) ^ 4 ∂μ := by
  have hmap : Measurable (fun ω => Real.exp (Y ω)) := by
    fun_prop
  have htest : Measurable (fun z : ℝ =>
      Real.exp (ρ * Real.log z) *
        (Real.exp (θ * Real.log z) - 1) ^ 4) := by
    fun_prop
  simpa only [Real.log_exp] using
    (MeasureTheory.integral_map (μ := μ)
      hmap.aemeasurable htest.aestronglyMeasurable)
