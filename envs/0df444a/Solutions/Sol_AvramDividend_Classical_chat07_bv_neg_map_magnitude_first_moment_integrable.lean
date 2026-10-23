-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_neg_map_magnitude_first_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:14:23.97469+00:00
-- url     : https://prove2.me/submissions/bcec6cd3-175d-42dd-90d6-03d6ea567085

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_min_abs_integrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The finite BV jump first moment transfers to positive magnitudes by negation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    Integrable (fun r : ℝ => min (1 : ℝ) r)
      ((X.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y)) := by
  have hneg : Measurable (fun y : ℝ => -y) := measurable_neg
  have hmin : Measurable (fun r : ℝ => min (1 : ℝ) r) :=
    measurable_const.min measurable_id
  apply (integrable_map_measure hmin.aestronglyMeasurable
    hneg.aemeasurable).2
  have heq : (fun y : ℝ => min (1 : ℝ) |y|) =ᵐ[
      X.ν.restrict (Iio (0 : ℝ))]
      (fun y : ℝ => min (1 : ℝ) (-y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    change y < (0 : ℝ) at hy
    simp only [abs_of_neg hy]
  simpa only [Function.comp_def] using
    (chat07_bv_negative_jump_min_abs_integrable X hBV).congr heq
