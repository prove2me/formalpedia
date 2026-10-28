-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_eq_stieltjes_of_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:55:19.145973+00:00
-- url     : https://prove2.me/submissions/1459d9d1-3ceb-4f11-9735-318fe0b57a70

import Mathlib.MeasureTheory.Measure.Stieltjes
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_realTime_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- An actual dividend strategy always enters the Stieltjes branch of dividendMeasure, because its real-time cumulative path is monotone. This eliminates the defensive zero-measure fallback in controlled payout calculations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    dividendMeasure D ω =
      (dividendStrategy_realTime_monotone D hD ω).stieltjesFunction.measure := by
  unfold dividendMeasure
  exact dif_pos (dividendStrategy_realTime_monotone D hD ω)
