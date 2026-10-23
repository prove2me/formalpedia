-- Prove2me | solution 1 for AvramDividend.Classical.chat06_unit_exponential_haslaw_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:48:12.878059+00:00
-- url     : https://prove2.me/submissions/769f53e7-bab1-4cb8-b5af-79b2c4e3070c

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.ENNReal.Operations
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal

/-- An exponential distribution with unit rate has its expected
real-time upper-tail survival probability for all nonnegative ages. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : Ω → ℝ)
    (hLaw : HasLaw X (expMeasure 1) P)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | t < X ω} = ENNReal.ofReal (Real.exp (-t)) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hExpLe : Real.exp (-t) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have hNonneg : 0 ≤ 1 - Real.exp (-t) := sub_nonneg.mpr hExpLe
  have hTailMeasure :
      (expMeasure 1) (Ioi t) =
        ENNReal.ofReal (Real.exp (-t)) := by
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
      ← ofReal_cdf (expMeasure 1) t,
      cdf_expMeasure_eq (by norm_num) t, if_pos ht]
    simp only [one_mul]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hNonneg]
    congr 1
    ring
  calc
    P {ω | t < X ω} = (P.map X) (Ioi t) := by
      rw [map_apply_of_aemeasurable hLaw.aemeasurable measurableSet_Ioi]
      rfl
    _ = (expMeasure 1) (Ioi t) := by rw [hLaw.map_eq]
    _ = ENNReal.ofReal (Real.exp (-t)) := hTailMeasure
