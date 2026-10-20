-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_restrict_Ioc_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:13:05.753405+00:00
-- url     : https://prove2.me/submissions/c60d6ef6-e69c-4fe5-929a-fe2e022c2fba

import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_restrict_Ioc_measurable
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
    (X : SpectrallyNegativeLevy P 𝓕) (l u : ℝ) :
    Measurable (fun ω : Ω =>
      (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) := by
  exact dividendMeasure_restrict_Ioc_measurable
    (runningSup X) (runningSup_isDividendStrategy X) l u
