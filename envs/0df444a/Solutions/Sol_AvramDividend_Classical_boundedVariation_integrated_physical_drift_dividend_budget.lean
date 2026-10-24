-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_integrated_physical_drift_dividend_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:50:35.324989+00:00
-- url     : https://prove2.me/submissions/c2470d69-67da-4c20-9198-50e7328a9cbd

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_boundedVariation_physical_hjb_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- BV physical drift and discounted dividend Stieltjes residuals give a
    nonpositive total budget along every active reserve path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (μtime μdiv : Measure ℝ) (u : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A, 0 < u t ∧ ENNReal.ofReal (u t) < C)
    (hTime : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) *
        (X.drift * deriv w (u t) +
          (∫ y in Iio (0 : ℝ), w (u t + y) - w (u t) ∂X.ν) -
          q * w (u t))) A μtime)
    (hDiv : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (1 - deriv w (u t))) A μdiv) :
    (∫ t in A, Real.exp (-(q * t)) *
        (X.drift * deriv w (u t) +
          (∫ y in Iio (0 : ℝ), w (u t + y) - w (u t) ∂X.ν) -
          q * w (u t)) ∂μtime) +
      (∫ t in A, Real.exp (-(q * t)) *
        (1 - deriv w (u t)) ∂μdiv) ≤ 0 := by
  have hgen : (∫ t in A, Real.exp (-(q * t)) *
        (X.drift * deriv w (u t) +
          (∫ y in Iio (0 : ℝ), w (u t + y) - w (u t) ∂X.ν) -
          q * w (u t)) ∂μtime) ≤ 0 := by
    apply MeasureTheory.integral_nonpos_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem hA] with t ht
    obtain ⟨ht0, htC⟩ := hregion t ht
    obtain ⟨_, hres, _⟩ :=
      boundedVariation_physical_hjb_budget X hBV q w C hw_hjb (u t) ht0 htC
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
      (sub_nonpos.mpr hres)
  have hdiv : (∫ t in A, Real.exp (-(q * t)) *
        (1 - deriv w (u t)) ∂μdiv) ≤ 0 := by
    apply MeasureTheory.integral_nonpos_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem hA] with t ht
    obtain ⟨ht0, htC⟩ := hregion t ht
    obtain ⟨_, _, hgrad⟩ :=
      boundedVariation_physical_hjb_budget X hBV q w C hw_hjb (u t) ht0 htC
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
      (sub_nonpos.mpr hgrad)
  exact add_nonpos hgen hdiv
