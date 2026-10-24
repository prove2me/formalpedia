-- Prove2me | solution 1 for AvramDividend.Classical.capped_hjb_discounted_generator_integral_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:47:11.106814+00:00
-- url     : https://prove2.me/submissions/a3a8c203-5171-4487-97e8-131e83245deb

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Integrating the discounted generator residual over any measurable region
    where the capped HJB inequality holds preserves its nonpositive sign. -/
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
    (hInt : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (X.generator w (u t) - q * w (u t))) A μ) :
    (∫ t in A, Real.exp (-(q * t)) *
      (X.generator w (u t) - q * w (u t)) ∂μ) ≤ 0 := by
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hA] with t ht
  obtain ⟨ht0, htC⟩ := hregion t ht
  obtain ⟨_, hgen, _⟩ :=
    hjb_component_inequalities X q w C hw_hjb (u t) ht0 htC
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
    hgen
