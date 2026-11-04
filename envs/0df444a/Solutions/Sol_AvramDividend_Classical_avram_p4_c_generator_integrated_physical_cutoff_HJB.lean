-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_integrated_physical_cutoff_HJB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:07:41.572171+00:00
-- url     : https://prove2.me/submissions/32aba039-07b4-4fe2-b19b-616704649644

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
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (μ : Measure ℝ) (u : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A, 0 < u t ∧ ENNReal.ofReal (u t) < C) :
    let G : ℝ → ℝ := fun t =>
      Real.exp (-(q * t)) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u t) +
          (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w (u t) +
          (∫ z in Iio (-ε), w (u t + z) - w (u t) ∂X.ν) +
          (∫ z in Ico (-ε) 0,
            SpectrallyNegativeLevy.generatorIntegrand w (u t) z ∂X.ν) -
          q * w (u t))
    IntegrableOn G A μ → (∫ t in A, G t ∂μ) ≤ 0 := by
  dsimp only
  intro hInt
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hA] with t ht
  obtain ⟨ht0, htC⟩ := hregion t ht
  obtain ⟨hint, hres⟩ := hw_gen (u t) ht0 htC
  have hFormula :=
    avram_p4_c_generator_original_epsilon_drift_compact
      X w (u t) ε hε hε1 hint
  rw [hFormula] at hres
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hres
