-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_two_adaptive_cutoffs_same_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:00:49.188206+00:00
-- url     : https://prove2.me/submissions/25a59546-18d4-45d8-857d-534a44a4c56c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_adaptive_cutoff_residual_L1_transport
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Any two state-dependent strict Levy truncations produce equal
integrable original discounted physical generator residual integrals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {α : Type*} [mα : MeasurableSpace α]
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y)
    (μ : Measure α) (clock u : α → ℝ) (A : Set α)
    (ε δ : α → ℝ)
    (hε : ∀ p ∈ A, 0 < ε p ∧ ε p < 1)
    (hδ : ∀ p ∈ A, 0 < δ p ∧ δ p < 1)
    (hA : MeasurableSet A)
    (hregion : ∀ p ∈ A, 0 < u p ∧ ENNReal.ofReal (u p) < C) :
    let F : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.generator w (u p) - q * w (u p))
    let phys : (α → ℝ) → α → ℝ := fun r p => Real.exp (-(q * clock p)) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-(r p)), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-(r p)), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-(r p)) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
    IntegrableOn F A μ →
      IntegrableOn (phys ε) A μ ∧ IntegrableOn (phys δ) A μ ∧
      (∫ p in A, phys ε p ∂μ) = (∫ p in A, phys δ p ∂μ) := by
  intro F phys hF
  have hfirst :=
    avram_p4_c_generator_adaptive_cutoff_residual_L1_transport
      X w q C hw_gen μ clock u A ε hε hA hregion hF
  have hsecond :=
    avram_p4_c_generator_adaptive_cutoff_residual_L1_transport
      X w q C hw_gen μ clock u A δ hδ hA hregion hF
  rcases hfirst with ⟨hI1, hEq1⟩
  rcases hsecond with ⟨hI2, hEq2⟩
  exact ⟨hI1, hI2, hEq1.trans hEq2.symm⟩
