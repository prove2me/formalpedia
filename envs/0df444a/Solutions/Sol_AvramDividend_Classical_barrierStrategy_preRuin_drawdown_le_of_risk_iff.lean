-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_preRuin_drawdown_le_of_risk_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:53:36.8687+00:00
-- url     : https://prove2.me/submissions/94b8156a-44f7-4c3d-b148-b1d26757a02b

import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The pre-ruin payment region never contains a breached drawdown barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ω : Ω) (u t : ℝ≥0)
    (hdraw : riskProcess X x (barrierStrategy X x a) (u + t) ω < 0 ↔
      a < runningSup X (u + t) ω - X.X (u + t) ω)
    (hbefore : ((u + t : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x (barrierStrategy X x a) ω) :
    runningSup X (u + t) ω - X.X (u + t) ω ≤ a := by
  have hnonneg :=
    riskProcess_nonnegative_strictly_before_ruin
      X x (barrierStrategy X x a) ω (u + t) hbefore
  apply le_of_not_gt
  intro hdraw_gt
  exact (not_lt_of_ge hnonneg) (hdraw.mpr hdraw_gt)
