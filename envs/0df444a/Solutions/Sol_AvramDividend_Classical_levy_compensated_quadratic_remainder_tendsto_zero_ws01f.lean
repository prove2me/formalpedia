-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_quadratic_remainder_tendsto_zero_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:27:31.088214+00:00
-- url     : https://prove2.me/submissions/d0c5d0a5-b62e-4afa-99c4-b390e6a86872

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_small_negative_jump_square_moment
import Theorems.Thm_AvramDividend_Classical_levy_small_negative_compensated_div_integrable
import Theorems.Thm_AvramDividend_Classical_compensated_exp_quadratic_ratio_tendsto_zero_ws01f

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Tendsto (fun n : ℕ =>
      ∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (((n : ℝ) + 1) * y) - 1 -
          ((n : ℝ) + 1) * y) / (((n : ℝ) + 1) ^ 2) ∂X.ν)
      atTop (nhds 0) := by
  let νs : Measure ℝ := X.ν.restrict (Ioo (-1 : ℝ) 0)
  have hmem : ∀ᵐ y ∂νs, y ∈ Ioo (-1 : ℝ) 0 := by
    exact ae_restrict_mem measurableSet_Ioo
  have hneg : ∀ᵐ y ∂νs, y < 0 := by
    filter_upwards [hmem] with y hy
    exact hy.2
  have hSq : Integrable (fun y : ℝ => y ^ 2) νs := by
    have hmeas : AEStronglyMeasurable (fun y : ℝ => y ^ 2) νs := by
      fun_prop
    have hnonneg : 0 ≤ᵐ[νs] (fun y : ℝ => y ^ 2) :=
      Filter.Eventually.of_forall (fun y => sq_nonneg y)
    exact (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp
      (ne_of_lt (finite_small_negative_jump_square_moment X.ν X.ν_integrable))
  have hInt (n : ℕ) : Integrable (fun y : ℝ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / (((n : ℝ) + 1) ^ 2)) νs := by
    have hd : 0 < (n : ℝ) + 1 := by positivity
    have hbase := levy_small_negative_compensated_div_integrable X
      ((n : ℝ) + 1) hd
    have hscaled : IntegrableOn (fun y : ℝ =>
        (((n : ℝ) + 1)⁻¹) *
          ((Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)))
        (Ioo (-1 : ℝ) 0) X.ν := hbase.const_mul _
    change IntegrableOn (fun y : ℝ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / (((n : ℝ) + 1) ^ 2))
      (Ioo (-1 : ℝ) 0) X.ν
    convert hscaled using 1
    ext y
    field_simp [ne_of_gt hd]
  exact compensated_exp_quadratic_ratio_tendsto_zero_ws01f νs hneg hSq hInt
