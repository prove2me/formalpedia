-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_weighted_exponential_image_support_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:02:00.442046+00:00
-- url     : https://prove2.me/submissions/a48e2b80-b108-488b-829c-ffd53da0e9fb

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_withDensity_restrict_negative_ae
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal

/-- The fourth-weighted original negative Levy marks have exponential image in the compact interval [0,1]. -/
theorem solution
    (ν : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᵐ z ∂(((ν.restrict (Set.Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp (θ * y) - 1) ^ 4))).map
      (fun y => Real.exp (θ * y))), z ∈ Set.Icc (0 : ℝ) 1 := by
  have hz : Measurable (fun y : ℝ => Real.exp (θ * y)) :=
    (Real.measurable_exp).comp (measurable_const.mul measurable_id)
  have hw : Measurable (fun y : ℝ =>
      ENNReal.ofReal ((Real.exp (θ * y) - 1) ^ 4)) :=
    ENNReal.measurable_ofReal.comp ((hz.sub_const 1).pow_const 4)
  have hnegative : ∀ᵐ y ∂(ν.restrict (Set.Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp (θ * y) - 1) ^ 4)), y < 0 :=
    AvramDividend.Classical.avram_p2_b_rate_withDensity_restrict_negative_ae ν _ hw
  refine (MeasureTheory.ae_map_iff hz.aemeasurable measurableSet_Icc).2 ?_
  filter_upwards [hnegative] with y hy
  constructor
  · exact le_of_lt (Real.exp_pos _)
  · have hmul : θ * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy)
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hmul)
