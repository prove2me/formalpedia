-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_realTime_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:46:07.04576+00:00
-- url     : https://prove2.me/submissions/a4b34a92-3d57-4993-b032-2a2f0bbad933

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_time_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The real-time extension of any dividend strategy path is measurable, with the same toNNReal convention used by dividendMeasure and its Stieltjes construction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Measurable (fun t : ℝ => D t.toNNReal ω) := by
  exact (dividendStrategy_time_measurable D hD ω).comp
    measurable_real_toNNReal
