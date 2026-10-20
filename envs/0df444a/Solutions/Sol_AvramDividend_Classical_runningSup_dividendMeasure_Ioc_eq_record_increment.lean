-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_record_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:18:45.994985+00:00
-- url     : https://prove2.me/submissions/1bc38b59-b399-4637-bce8-47e9bfbb4d8f

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_rightLim
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq
import Mathlib.Data.ENNReal.Basic
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
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ) :
    (dividendMeasure (runningSup X) ω) (Set.Ioc s t) =
      ENNReal.ofReal
        (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) := by
  rw [runningSup_dividendMeasure_Ioc_rightLim X ω s t]
  rw [runningSup_realTime_rightLim_eq X ω t]
  rw [runningSup_realTime_rightLim_eq X ω s]
