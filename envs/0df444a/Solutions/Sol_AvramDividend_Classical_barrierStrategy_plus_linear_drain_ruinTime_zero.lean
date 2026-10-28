-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_plus_linear_drain_ruinTime_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:32:01.895519+00:00
-- url     : https://prove2.me/submissions/245d4b13-0e9c-46da-b207-409cf37968c2

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_zero_of_negative_every_positive_time
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_reserve_negative
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The overpaying zero-barrier strategy has zero ruin time on every path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (ω : Ω) :
    ruinTime X x
      (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω = 0 := by
  exact ruinTime_zero_of_negative_every_positive_time X x
    (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω
    (barrierStrategy_plus_linear_drain_reserve_negative X x hx ω)
