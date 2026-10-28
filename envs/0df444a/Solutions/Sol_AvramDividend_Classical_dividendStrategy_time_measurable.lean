-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_time_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:43:53.650984+00:00
-- url     : https://prove2.me/submissions/7a0a0c4a-2ff3-4c32-ab2e-96e12ceae5d7

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every admissible dividend strategy has a Borel-measurable cumulative dividend path in time, since that path is nondecreasing. This is needed for measurable controlled reserve selectors and Stieltjes localisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Measurable (fun t : ℝ≥0 => D t ω) := by
  exact (hD.2.1 ω).measurable
