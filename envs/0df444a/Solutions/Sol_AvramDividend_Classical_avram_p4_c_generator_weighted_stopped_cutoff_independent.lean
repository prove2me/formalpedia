-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_weighted_stopped_cutoff_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:36:56.803204+00:00
-- url     : https://prove2.me/submissions/95c3f194-4a91-4d17-8d6c-212d713a15fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_weighted_physical_L1_and_sign
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original epsilon-physical stopped generator drift is integrable,
has nonpositive total integral and is cutoff independent with discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {α : Type*} [mα : MeasurableSpace α]
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (μ : Measure α) (u a : α → ℝ) (A : Set α)
    (hA : MeasurableSet A)
    (hregion : ∀ p ∈ A, 0 < u p ∧ ENNReal.ofReal (u p) < C)
    (ha : ∀ p ∈ A, 0 ≤ a p) :
    let F : α → ℝ := fun p =>
      a p * (X.generator w (u p) - q * w (u p))
    let phys : ℝ → α → ℝ := fun r p => a p *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-r), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-r), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-r) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
    IntegrableOn F A μ →
      IntegrableOn (phys ε) A μ ∧ IntegrableOn (phys δ) A μ ∧
      (∫ p in A, phys ε p ∂μ) = (∫ p in A, phys δ p ∂μ) ∧
      (∫ p in A, phys ε p ∂μ) ≤ 0 := by
  intro F phys hF
  have hfirst :=
    avram_p4_c_generator_weighted_physical_L1_and_sign
      X w q C hw_gen ε hε hε1 μ u a A hA hregion ha hF
  have hsecond :=
    avram_p4_c_generator_weighted_physical_L1_and_sign
      X w q C hw_gen δ hδ hδ1 μ u a A hA hregion ha hF
  rcases hfirst with ⟨hI1, hEq1, hneg1⟩
  rcases hsecond with ⟨hI2, hEq2, _⟩
  exact ⟨hI1, hI2, hEq1.trans hEq2.symm, hneg1⟩
