-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat25_finite_activity_physical_drift_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T16:52:17.142417+00:00
-- url     : https://prove2.me/submissions/df07c662-d566-4d73-b4e3-f0f0fea1dd53

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ) (hw_nonneg : ∀ z, 0 ≤ w z)
    (q y : ℝ) (hGen : X.GeneratorIntegrable w y)
    (hHJB : X.generator w y - q * w y ≤ 0) :
    X.drift * deriv w y ≤
      (q + (X.ν (Iio (0 : ℝ))).toReal) * w y := by
  have hInc : IntegrableOn (fun z : ℝ => w (y + z) - w y) (Iio 0) X.ν :=
    AvramDividend.Classical.boundedVariation_full_negative_jump_increment_integrable
      X hBV w y hGen
  have hConst : IntegrableOn (fun _ : ℝ => -(w y)) (Iio 0) X.ν :=
    MeasureTheory.integrableOn_const (ne_of_lt hFinite)
  have hPoint : (fun _ : ℝ => -(w y)) ≤ᵐ[X.ν.restrict (Iio 0)]
      (fun z : ℝ => w (y + z) - w y) := by
    exact Filter.Eventually.of_forall (fun z => by
      dsimp
      linarith [hw_nonneg (y + z)])
  have hMono := MeasureTheory.integral_mono_ae hConst hInc hPoint
  have hConstValue :
      (∫ z in Iio (0 : ℝ), -(w y) ∂X.ν) =
        - (X.ν (Iio (0 : ℝ))).toReal * w y := by
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real, smul_eq_mul]
  rw [hConstValue] at hMono
  have hPhysical :=
    AvramDividend.Classical.boundedVariation_generator_physical_drift_representation
      X hBV w y hGen
  rw [hPhysical] at hHJB
  calc
    X.drift * deriv w y ≤
        q * w y - (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) := by
          linarith
    _ ≤ q * w y + (X.ν (Iio (0 : ℝ))).toReal * w y := by
          linarith
    _ = (q + (X.ν (Iio (0 : ℝ))).toReal) * w y := by ring
