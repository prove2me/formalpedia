-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_Ioc_nonpos_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:29:45.263163+00:00
-- url     : https://prove2.me/submissions/1bbe3158-d54e-4040-9539-95aac7bb9b92

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- Every interval entirely before or ending at time zero has zero regulator mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ) (hs : s ≤ 0) (ht : t ≤ 0) :
    (dividendMeasure (runningSup X) ω) (Set.Ioc s t) = 0 := by
  rw [runningSup_dividendMeasure_Ioc_eq_record_increment X ω s t]
  rw [Real.toNNReal_of_nonpos ht, Real.toNNReal_of_nonpos hs]
  simp
