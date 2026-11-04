-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_physical_residual_L1_transport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:14:05.644618+00:00
-- url     : https://prove2.me/submissions/4daf5e58-cf1c-43f3-9726-587dec1182bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_original_epsilon_drift_compact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {α : Type*} [mα : MeasurableSpace α]
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (μ : Measure α) (clock u : α → ℝ) (A : Set α)
    (hA : MeasurableSet A)
    (hregion : ∀ p ∈ A, 0 < u p ∧ ENNReal.ofReal (u p) < C) :
    let F : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.generator w (u p) - q * w (u p))
    let G : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-ε), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
    IntegrableOn F A μ →
      IntegrableOn G A μ ∧ (∫ p in A, G p ∂μ) = (∫ p in A, F p ∂μ) := by
  let F : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.generator w (u p) - q * w (u p))
  let G : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-ε), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
  change IntegrableOn F A μ →
    IntegrableOn G A μ ∧ (∫ p in A, G p ∂μ) = (∫ p in A, F p ∂μ)
  intro hF
  have hEq : Set.EqOn F G A := by
    intro p hp
    obtain ⟨hp0, hpC⟩ := hregion p hp
    have hI := hw_gen (u p) hp0 hpC
    dsimp [F, G]
    rw [avram_p4_c_generator_original_epsilon_drift_compact
      X w (u p) ε hε hε1 hI]
  refine ⟨hF.congr_fun hEq hA, ?_⟩
  exact (MeasureTheory.setIntegral_congr_fun hA hEq).symm
