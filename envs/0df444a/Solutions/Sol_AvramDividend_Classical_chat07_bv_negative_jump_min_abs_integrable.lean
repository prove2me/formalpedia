-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_negative_jump_min_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:39:46.216591+00:00
-- url     : https://prove2.me/submissions/370328a4-609b-4ec9-a34a-700e2fec75b8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_jump_magnitude_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => min 1 |y|) (Iio 0) X.ν := by
  have hfinite := bv_jump_magnitude_integrable X hBV
  have hmap : Measurable (fun y : ℝ => Real.toNNReal (-y)) :=
    measurable_real_toNNReal.comp measurable_neg
  have hweight :
      Measurable (fun z : ℝ≥0 => ENNReal.ofReal (min (z : ℝ) 1)) := by
    fun_prop
  rw [lintegral_map hweight hmap] at hfinite
  refine ⟨(measurable_const.min measurable_abs).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal ‖min (1 : ℝ) |y|‖ ∂X.ν)
        = (∫⁻ y in Iio (0 : ℝ),
            ENNReal.ofReal (min ((Real.toNNReal (-y) : ℝ≥0) : ℝ) 1) ∂X.ν) := by
          apply setLIntegral_congr_fun measurableSet_Iio
          intro y hy
          have hyneg : y < 0 := hy
          have hz : 0 ≤ min (1 : ℝ) |y| :=
            le_min (by norm_num) (abs_nonneg _)
          change ENNReal.ofReal ‖min (1 : ℝ) |y|‖ =
            ENNReal.ofReal (min ((Real.toNNReal (-y) : ℝ≥0) : ℝ) 1)
          rw [Real.norm_eq_abs, abs_of_nonneg hz,
            Real.coe_toNNReal', max_eq_left (by linarith)]
          rw [abs_of_neg hyneg, min_comm]
    _ < ⊤ := hfinite
