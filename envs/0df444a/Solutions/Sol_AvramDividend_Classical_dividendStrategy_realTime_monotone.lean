-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_realTime_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:50:57.820663+00:00
-- url     : https://prove2.me/submissions/ec4c78d2-1645-4ffd-96e3-c54aceb24f16

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The real-time cumulative dividend extension used by dividendMeasure is monotone, as Real.toNNReal and every dividend-strategy path are monotone. Thus the Stieltjes measure never selects its fallback zero branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Monotone (fun t : ℝ => D t.toNNReal ω) := by
  intro s t hst
  exact (hD.2.1 ω) (Real.toNNReal_le_toNNReal hst)
