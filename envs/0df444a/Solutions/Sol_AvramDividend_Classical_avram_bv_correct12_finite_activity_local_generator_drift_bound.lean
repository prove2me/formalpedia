-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_correct12_finite_activity_local_generator_drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T20:11:02.468503+00:00
-- url     : https://prove2.me/submissions/b379a673-a44c-446e-8954-e9d8413ea490

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (y : ℝ)
    (hGen : X.GeneratorIntegrable w y)
    (hHJB : X.generator w y - q * w y ≤ 0)
    (hLocal : ∀ z : ℝ, z < 0 → 0 ≤ w (y + z)) :
    X.drift * deriv w y ≤
      (q + (X.ν (Iio (0 : ℝ))).toReal) * w y := by
  classical
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hFinite⟩
  have hConst : Integrable (fun _ : ℝ => -w y) μ :=
    integrable_const _
  have hIncr : Integrable (fun z : ℝ => w (y + z) - w y) μ := by
    simpa [μ, IntegrableOn] using
      (boundedVariation_full_negative_jump_increment_integrable X hBV w y hGen)
  have hMono :
      (∫ _ : ℝ, -w y ∂μ) ≤
        (∫ z : ℝ, w (y + z) - w y ∂μ) := by
    apply integral_mono_ae hConst hIncr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iio] with z hz
    have hzneg : z < 0 := hz
    linarith [hLocal z hzneg]
  have hJump :
      -((X.ν (Iio (0 : ℝ))).toReal) * w y ≤
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) := by
    simpa [μ, integral_const, Measure.real_def, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using hMono
  have hRep :=
    boundedVariation_generator_physical_drift_representation X hBV w y hGen
  rw [hRep] at hHJB
  nlinarith
