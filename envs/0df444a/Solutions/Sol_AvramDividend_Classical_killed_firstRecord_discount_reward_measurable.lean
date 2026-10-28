-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_discount_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:55:29.487107+00:00
-- url     : https://prove2.me/submissions/d6ddc673-5b16-4233-a1ec-399a59241173

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Measurability of the stopped first-record discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b ε q : ℝ) :
    Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0) := by
  have hT : Measurable (twoSidedExitUpTime X b) :=
    ((upperPassage_stopping_rightCont_filtration X b).measurable).mono
      (upperPassage_stopping_rightCont_filtration X b).measurableSpace_le
      le_rfl
  have hR : Measurable (barrierRuinTime X a) :=
    barrierRuinTime_measurable X a
  have hTime : Measurable
      (fun ω : Ω => (twoSidedExitUpTime X b ω).toReal) :=
    ENNReal.measurable_toReal.comp hT
  have hExp : Measurable
      (fun ω : Ω => ε * Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal))) :=
    measurable_const.mul
      (Real.measurable_exp.comp ((measurable_const.mul hTime).neg))
  exact (ENNReal.measurable_ofReal.comp hExp).ite
    (measurableSet_lt hT hR) measurable_const
