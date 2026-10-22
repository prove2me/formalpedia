-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_generator_first_order_dominated_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:43:22.780564+00:00
-- url     : https://prove2.me/submissions/e564cbab-3499-4db0-a57d-3edf1363190c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_jump_magnitude_integrable
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! First-order Lévy generator domination in the BV branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (f : ℝ → ℝ) (x C : ℝ) (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable
      (SpectrallyNegativeLevy.generatorIntegrand f x)
      (X.ν.restrict (Iio 0)))
    (hbound : ∀ᵐ y ∂X.ν.restrict (Iio 0),
      ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
        C * min 1 |y|) :
    X.GeneratorIntegrable f x := by
  have hw : IntegrableOn (fun y : ℝ => min 1 |y|) (Iio 0) X.ν := by
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
  change Integrable
    (SpectrallyNegativeLevy.generatorIntegrand f x)
    (X.ν.restrict (Iio 0))
  have hdom :
      Integrable (fun y : ℝ => C * min 1 |y|)
        (X.ν.restrict (Iio 0)) := hw.const_mul C
  apply hdom.mono hmeas
  filter_upwards [hbound] with y hy
  have hmin0 : 0 ≤ min (1 : ℝ) |y| := by positivity
  simpa only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hC, abs_of_nonneg hmin0] using hy
