-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_Ioc_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:33:09.512041+00:00
-- url     : https://prove2.me/submissions/f2336125-aead-454f-9a8c-d7446a3098f2

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
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
    (dividendMeasure (runningSup X) ω) (Set.Ioc s t) < ⊤ := by
  rw [runningSup_dividendMeasure_Ioc_eq_record_increment X ω s t]
  exact ENNReal.ofReal_lt_top
