-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_hessian_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:50:54.859736+00:00
-- url     : https://prove2.me/submissions/dc563861-bed1-4d60-986f-c7538cfb37d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Pathwise stopped original Gaussian correction has finite integral
once true interior localisation, time measure and measurability are supplied. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (μ : Measure ℝ≥0) (ω : Ω)
    (hμ : μ (Iio (τ ω)) < ⊤)
    (hPath : ∀ᵐ s ∂μ.restrict (Iio (τ ω)),
      riskProcess X x D s ω ∈ Icc a b)
    (hMeas : AEStronglyMeasurable
      (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (riskProcess X x D s ω))) (μ.restrict (Iio (τ ω)))) :
    IntegrableOn
      (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (riskProcess X x D s ω))) (Iio (τ ω)) μ := by
  obtain ⟨K, hK, hBound⟩ :=
    avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
      X q hq C w hwC2 a b hBand
  refine IntegrableOn.of_bound hμ hMeas K ?_
  filter_upwards [hPath] with s hs
  simpa only [Real.norm_eq_abs] using
    (hBound s (riskProcess X x D s ω) hs)
