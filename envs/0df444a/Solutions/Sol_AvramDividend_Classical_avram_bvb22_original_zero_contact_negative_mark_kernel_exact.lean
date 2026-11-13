-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_original_zero_contact_negative_mark_kernel_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:17:04.032706+00:00
-- url     : https://prove2.me/submissions/7c40911c-1abe-4545-936d-3ef59253c7c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_neg : ∀ z < 0, w z = 0)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν) =
      -(w 0) * (X.ν (Iio (0 : ℝ))).toReal := by
  have hpoint : ∀ z ∈ Iio (0 : ℝ),
      w ((0 : ℝ) + z) - w 0 = -(w 0) := by
    intro z hz
    simp [hw_neg z hz]
  calc
    (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν)
        = ∫ z in Iio (0 : ℝ), -(w 0) ∂X.ν := by
          apply setIntegral_congr_fun measurableSet_Iio
          intro z hz
          exact hpoint z hz
    _ = -(w 0) * (X.ν (Iio (0 : ℝ))).toReal := by
          simp [integral_const, Measure.real_def, smul_eq_mul, mul_comm]
