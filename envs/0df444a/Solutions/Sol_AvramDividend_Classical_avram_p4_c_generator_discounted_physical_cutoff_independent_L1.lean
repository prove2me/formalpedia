-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_discounted_physical_cutoff_independent_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:40:10.306568+00:00
-- url     : https://prove2.me/submissions/2e9e4fa1-e7eb-4e72-8f93-0b404524b9b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_physical_residual_L1_transport
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every strict truncation gives the same original discounted generator
integral on a measured stopped region, without HJB sign assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {α : Type*} [mα : MeasurableSpace α]
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (μ : Measure α) (clock u : α → ℝ) (A : Set α)
    (hA : MeasurableSet A)
    (hregion : ∀ p ∈ A, 0 < u p ∧ ENNReal.ofReal (u p) < C) :
    let F : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.generator w (u p) - q * w (u p))
    let phys : ℝ → α → ℝ := fun r p => Real.exp (-(q * clock p)) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-r), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-r), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-r) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
    IntegrableOn F A μ →
      IntegrableOn (phys ε) A μ ∧ IntegrableOn (phys δ) A μ ∧
      (∫ p in A, phys ε p ∂μ) = (∫ p in A, phys δ p ∂μ) := by
  intro F phys hF
  have hfirst :=
    avram_p4_c_generator_physical_residual_L1_transport
      X w q C hw_gen ε hε hε1 μ clock u A hA hregion hF
  have hsecond :=
    avram_p4_c_generator_physical_residual_L1_transport
      X w q C hw_gen δ hδ hδ1 μ clock u A hA hregion hF
  rcases hfirst with ⟨hI1, hEq1⟩
  rcases hsecond with ⟨hI2, hEq2⟩
  exact ⟨hI1, hI2, hEq1.trans hEq2.symm⟩
