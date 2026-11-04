-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_adaptive_cutoff_residual_L1_transport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:42:54.189418+00:00
-- url     : https://prove2.me/submissions/6fd98a53-9d2d-4c6c-bb7e-f008c1320231

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_original_epsilon_drift_compact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A state-dependent strict jump cutoff preserves exactly the original
discounted Levy generator residual and its stopped L1 integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {α : Type*} [mα : MeasurableSpace α]
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y)
    (μ : Measure α) (clock u : α → ℝ) (A : Set α)
    (ε : α → ℝ)
    (hε : ∀ p ∈ A, 0 < ε p ∧ ε p < 1)
    (hA : MeasurableSet A)
    (hregion : ∀ p ∈ A, 0 < u p ∧ ENNReal.ofReal (u p) < C) :
    let F : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.generator w (u p) - q * w (u p))
    let G : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-(ε p)), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-(ε p)), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-(ε p)) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
    IntegrableOn F A μ →
      IntegrableOn G A μ ∧
      (∫ p in A, G p ∂μ) = (∫ p in A, F p ∂μ) := by
  let F : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.generator w (u p) - q * w (u p))
  let G : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-(ε p)), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-(ε p)), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-(ε p)) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
  change IntegrableOn F A μ →
    IntegrableOn G A μ ∧
    (∫ p in A, G p ∂μ) = (∫ p in A, F p ∂μ)
  intro hF
  have hEq : Set.EqOn F G A := by
    intro p hp
    obtain ⟨hp0, hpC⟩ := hregion p hp
    obtain ⟨hpε, hpε1⟩ := hε p hp
    dsimp [F, G]
    rw [avram_p4_c_generator_original_epsilon_drift_compact
      X w (u p) (ε p) hpε hpε1 (hw_gen (u p) hp0 hpC)]
  exact ⟨hF.congr_fun hEq hA,
    (MeasureTheory.setIntegral_congr_fun hA hEq).symm⟩
