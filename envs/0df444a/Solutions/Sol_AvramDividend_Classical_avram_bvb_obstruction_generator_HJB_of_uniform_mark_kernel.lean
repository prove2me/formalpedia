-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_generator_HJB_of_uniform_mark_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:11:38.292307+00:00
-- url     : https://prove2.me/submissions/4eafdfe4-ecd3-41a0-a116-234bda4bfcde

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_negative_mark_affine_scalar_hjb_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (y : ℝ) (hy : 0 < y) (w : ℝ → ℝ)
    (hσ : X.σ = 0) (hc : X.c = 1 / 2)
    (hw : w y = 1 / 2 + y) (hd : deriv w y = 1)
    (hJump : (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
      if y < 1 then y * (y - 1) / 2 else 0) :
    X.generator w y - w y ≤ 0 := by
  have hScalar :=
    avram_bvb_obstruction_uniform_negative_mark_affine_scalar_hjb_nonpos y hy
  have hFormula :
      X.generator w y - w y =
      (1 / 2 : ℝ) + (if y < 1 then y * (y - 1) / 2 else 0)
         - (1 / 2 + y) := by
    change X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
      X.c * deriv w y +
      (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν)
      - w y = _
    rw [hσ, hc, hd, hw, hJump]
    ring
  rw [hFormula]
  split_ifs at hScalar ⊢ <;> nlinarith
