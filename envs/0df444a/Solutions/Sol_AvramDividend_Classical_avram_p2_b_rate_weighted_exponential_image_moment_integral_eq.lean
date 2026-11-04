-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_moment_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:12:25.713918+00:00
-- url     : https://prove2.me/submissions/ebb902d3-21b9-4222-b684-f41a8f859176

import Mathlib.Tactic.Positivity
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (θ : ℝ) (k : ℕ)
    (hInt : Integrable (fun ω =>
      (Real.exp (θ * Y ω)) ^ k *
        (Real.exp (θ * Y ω) - 1) ^ 4) μ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((μ.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * Y ω)))) =
    ENNReal.ofReal (∫ ω,
      (Real.exp (θ * Y ω)) ^ k *
        (Real.exp (θ * Y ω) - 1) ^ 4 ∂μ) := by
  rw [AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_lintegral
    μ Y hY θ k]
  have heq :
      (∫⁻ ω, ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4) *
        ENNReal.ofReal ((Real.exp (θ * Y ω)) ^ k) ∂μ) =
      (∫⁻ ω, ENNReal.ofReal
        ((Real.exp (θ * Y ω)) ^ k *
          (Real.exp (θ * Y ω) - 1) ^ 4) ∂μ) := by
    apply lintegral_congr_ae
    filter_upwards [] with ω
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [heq]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hInt (Filter.Eventually.of_forall (fun ω => by positivity))).symm
