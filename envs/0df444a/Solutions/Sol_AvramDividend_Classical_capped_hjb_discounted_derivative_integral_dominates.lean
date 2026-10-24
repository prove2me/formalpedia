-- Prove2me | solution 1 for AvramDividend.Classical.capped_hjb_discounted_derivative_integral_dominates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:45:30.925642+00:00
-- url     : https://prove2.me/submissions/9d0b635f-d00b-4d25-b1b2-bde18ec71716

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A capped HJB supergradient dominates discounted dividends integrated
    against any measure, including Stieltjes measures with singular mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (μ : Measure ℝ) (u : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A, 0 < u t ∧ ENNReal.ofReal (u t) < C)
    (hExp : IntegrableOn (fun t : ℝ => Real.exp (-(q * t))) A μ)
    (hDer : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * deriv w (u t)) A μ) :
    (∫ t in A, Real.exp (-(q * t)) ∂μ) ≤
      ∫ t in A, Real.exp (-(q * t)) * deriv w (u t) ∂μ := by
  apply MeasureTheory.integral_mono_ae hExp hDer
  filter_upwards [MeasureTheory.ae_restrict_mem hA] with t ht
  obtain ⟨ht0, htC⟩ := hregion t ht
  obtain ⟨_, _, hgrad⟩ :=
    hjb_component_inequalities X q w C hw_hjb (u t) ht0 htC
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hgrad (le_of_lt (Real.exp_pos _))
