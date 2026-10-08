-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_barrier_piecewise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:32:21.126483+00:00
-- url     : https://prove2.me/submissions/3610e1d0-014f-4511-a6cc-2d913d934d5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
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
    (x a : ℝ) (hxa : x ≤ a) (t : ℝ≥0) (ht : 0 < t) (ω : Ω) :
    riskProcess X x (barrierStrategy X x a) t ω =
      if runningSup X t ω < a - x then
        x + X.X t ω
      else
        a + X.X t ω - runningSup X t ω := by
  classical
  by_cases hbefore : runningSup X t ω < a - x
  · rw [if_pos hbefore]
    have hraw := (runningSup_eq_rawSup_nonneg X t ω).1
    let S : ℝ := ⨆ s : Icc (0 : ℝ≥0) t, X.X s ω
    have hbelowRaw : S < a - x := by
      dsimp [S]
      simpa only [hraw] using hbefore
    have hnonpos : x - a + S ≤ 0 := by linarith
    have hD : barrierStrategy X x a t ω = 0 := by
      change (if t = 0 then 0 else max 0 (x - a + S)) = 0
      rw [if_neg (ne_of_gt ht)]
      exact max_eq_left hnonpos
    change x + X.X t ω - barrierStrategy X x a t ω =
      x + X.X t ω
    rw [hD, sub_zero]
  · rw [if_neg hbefore]
    exact riskProcess_barrier_after_crossing X x a hxa t ht ω
      (le_of_not_gt hbefore)
