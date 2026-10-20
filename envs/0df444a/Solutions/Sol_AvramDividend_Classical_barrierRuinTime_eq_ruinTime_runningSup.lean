-- Prove2me | solution 1 for AvramDividend.Classical.barrierRuinTime_eq_ruinTime_runningSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:06:18.257481+00:00
-- url     : https://prove2.me/submissions/06c8fde6-7af5-437a-8b40-cde9ccefff82

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
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
    barrierRuinTime X a = ruinTime X a (runningSup X) := by
  funext ω
  simp [ruinTime, riskProcess, barrierRuinTime, drawdown,
    reflectedSup, sub_lt_zero, lt_sub_iff_add_lt]
