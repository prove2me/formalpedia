-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_real_lintegral_conversion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:49:38.392087+00:00
-- url     : https://prove2.me/submissions/d3c6a42a-e360-4ee4-83f9-5c1d54cfe032

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) (hpositive : ∀ᵐ z ∂μ, 0 ≤ z)
    (k : ℕ) (hk : Integrable (fun z : ℝ => z ^ k) μ) :
    (∫ z : ℝ, z ^ k ∂μ) =
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ).toReal := by
  have hnonneg : ∀ᵐ z ∂μ, 0 ≤ z ^ k :=
    hpositive.mono (fun z hz => pow_nonneg hz k)
  have hmeas : AEStronglyMeasurable (fun z : ℝ => z ^ k) μ := by
    fun_prop
  have hreal :=
    integral_eq_lintegral_of_nonneg_ae hnonneg hmeas
  have hpow : ∀ᵐ z ∂μ,
      ENNReal.ofReal (z ^ k) = (ENNReal.ofReal z) ^ k := by
    filter_upwards [hpositive] with z hz
    exact ENNReal.ofReal_pow hz k
  calc
    (∫ z : ℝ, z ^ k ∂μ) =
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂μ).toReal := hreal
    _ = (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ).toReal := by
      congr 1
      exact lintegral_congr_ae hpow
