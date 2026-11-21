-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_large_negative_jump_generator_integral_lower_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:41:03.509616+00:00
-- url     : https://prove2.me/submissions/03f2fdef-dc8e-411e-9309-c773d3199169

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (y : ℝ)
    (hwpos : ∀ u : ℝ, 0 ≤ w u)
    (hderiv : 0 ≤ deriv w y)
    (hGen : X.GeneratorIntegrable w y) :
    -(X.ν (Iic (-1 : ℝ))).toReal * w y ≤
      ∫ z in Iic (-1 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by
  have hSubset : Iic (-1 : ℝ) ⊆ Iio (0 : ℝ) := by
    intro z hz
    change z ≤ (-1 : ℝ) at hz
    change z < 0
    exact lt_of_le_of_lt hz (by norm_num)
  have hLarge :
      IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w y)
        (Iic (-1 : ℝ)) X.ν :=
    hGen.mono_set hSubset
  have hUnit :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (-1 : ℝ)) X.ν :=
    levy_large_negative_jump_unit_integrable X
  have hConst :
      IntegrableOn (fun _ : ℝ => -(w y)) (Iic (-1 : ℝ)) X.ν := by
    change Integrable (fun _ : ℝ => -(w y))
      (X.ν.restrict (Iic (-1 : ℝ)))
    simpa only [mul_one] using hUnit.const_mul (-(w y))
  have hPoint : ∀ z ∈ Iic (-1 : ℝ),
      -(w y) ≤ SpectrallyNegativeLevy.generatorIntegrand w y z := by
    intro z hz
    have hNot : z ∉ Ioo (-1 : ℝ) 1 := by
      intro hi
      exact (not_lt_of_ge hz) hi.1
    dsimp [SpectrallyNegativeLevy.generatorIntegrand]
    simp only [Set.indicator_of_notMem hNot, mul_zero, sub_zero]
    linarith [hwpos (y + z)]
  have hAE : ∀ᵐ z ∂(X.ν.restrict (Iic (-1 : ℝ))),
      -(w y) ≤ SpectrallyNegativeLevy.generatorIntegrand w y z := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
    exact hPoint z hz
  have hIntegral :=
    integral_mono_ae hConst hLarge hAE
  have hMass :
      (∫ z in Iic (-1 : ℝ), -(w y) ∂X.ν) =
        -(X.ν (Iic (-1 : ℝ))).toReal * w y := by
    simp [integral_const, smul_eq_mul, Measure.real_def]
  rw [← hMass]
  exact hIntegral
