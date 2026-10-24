-- Prove2me | solution 1 for AvramDividend.Classical.chat08_killed_first_record_discount_weight_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:09:42.123985+00:00
-- url     : https://prove2.me/submissions/691989df-5c25-4783-86dc-b510d3b239ba

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical

/-! A killed discounted first-record payment is measurable for every threshold and barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a c q h : ℝ) :
    Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
        ENNReal.ofReal (h * Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
      else 0) := by
  have hu : Measurable (twoSidedExitUpTime X c) :=
    chat08_upper_passage_clock_measurable X c
  have hτ : Measurable (barrierRuinTime X a) := barrierRuinTime_measurable X a
  have hevent : MeasurableSet
      {ω : Ω | twoSidedExitUpTime X c ω < barrierRuinTime X a ω} :=
    measurableSet_lt hu hτ
  have htime : Measurable (fun ω : Ω => (twoSidedExitUpTime X c ω).toReal) :=
    hu.ennreal_toReal
  have hweight : Measurable (fun ω : Ω =>
      ENNReal.ofReal (h * Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))) := by
    have hm : Measurable (fun ω : Ω => q * (twoSidedExitUpTime X c ω).toReal) :=
      measurable_const.mul htime
    exact (measurable_const.mul hm.neg.exp).ennreal_ofReal
  exact Measurable.ite hevent hweight measurable_const
