-- Prove2me | solution 1 for AvramDividend.Classical.barrier_ruin_iff_drawdown_after_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:43:23.0804+00:00
-- url     : https://prove2.me/submissions/22192d07-24cc-478a-9ba2-8c897ec634e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_riskProcess_barrier_after_crossing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (t : ℝ≥0) (ht : 0 < t) (ω : Ω)
    (hcross : a - x ≤ runningSup X t ω) :
    (riskProcess X x (barrierStrategy X x a) t ω < 0 ↔
      a < runningSup X t ω - X.X t ω) := by
  have hU :=
    riskProcess_barrier_after_crossing X x a hxa t ht ω hcross
  rw [hU]
  constructor
  · intro h
    linarith
  · intro h
    linarith
