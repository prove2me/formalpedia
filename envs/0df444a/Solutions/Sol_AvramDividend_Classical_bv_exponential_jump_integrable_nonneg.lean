-- Prove2me | solution 1 for AvramDividend.Classical.bv_exponential_jump_integrable_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:25:27.618514+00:00
-- url     : https://prove2.me/submissions/e2cd4342-17d4-423d-95c7-56f208ae50c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) X.ν := by
  by_cases h1 : 1 ≤ θ
  · exact bv_exponential_jump_integrable X hbv θ h1
  have hsmall : θ ≤ 1 := le_of_lt (lt_of_not_ge h1)
  have hbase :
      IntegrableOn (fun y : ℝ => Real.exp y - 1)
        (Iio (0 : ℝ)) X.ν := by
    simpa only [one_mul] using
      (bv_exponential_jump_integrable X hbv 1 (le_refl (1 : ℝ)))
  have hmajor :
      ∀ᵐ y ∂X.ν.restrict (Iio (0 : ℝ)),
        ‖Real.exp (θ * y) - 1‖ ≤ ‖Real.exp y - 1‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    have hy0 : y ≤ 0 := le_of_lt hy
    have hθy : y ≤ θ * y := by
      have h := mul_le_mul_of_nonpos_right hsmall hy0
      simpa only [one_mul] using h
    have hxle : Real.exp y ≤ Real.exp (θ * y) :=
      Real.exp_le_exp.mpr hθy
    have hyexp : Real.exp y ≤ 1 :=
      Real.exp_le_one_iff.mpr hy0
    have hθexp : Real.exp (θ * y) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ hy0)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  exact Integrable.mono hbase (by fun_prop) hmajor
