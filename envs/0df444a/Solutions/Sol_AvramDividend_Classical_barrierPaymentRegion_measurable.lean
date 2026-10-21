-- Prove2me | solution 1 for AvramDividend.Classical.barrierPaymentRegion_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:47:06.3837+00:00
-- url     : https://prove2.me/submissions/d8bc6c9f-6ed2-477d-851e-318a0af29d0c

import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) :
    MeasurableSet
      {p : ℝ × Ω |
        p.1 ∈ paymentTimes (barrierRuinTime X a p.2)} := by
  exact paymentTimes_joint_measurable
    (barrierRuinTime X a) (barrierRuinTime_measurable X a)
