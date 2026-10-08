-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_barrier_after_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T17:51:22.453249+00:00
-- url     : https://prove2.me/submissions/b69a1110-cc27-41b1-b9a4-2573c5cd55e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (t : ℝ≥0) (ht : 0 < t) (ω : Ω)
    (hcross : a - x ≤ runningSup X t ω) :
    riskProcess X x (barrierStrategy X x a) t ω =
      a + X.X t ω - runningSup X t ω := by
  classical
  have hraw := (runningSup_eq_rawSup_nonneg X t ω).1
  let S : ℝ := ⨆ s : Icc (0 : ℝ≥0) t, X.X s ω
  have hcrossRaw : a - x ≤ S := by
    dsimp [S]
    simpa only [hraw] using hcross
  have hnonneg : 0 ≤ x - a + S := by linarith
  have hD : barrierStrategy X x a t ω = x - a + S := by
    change (if t = 0 then 0 else max 0 (x - a + S)) = _
    rw [if_neg (ne_of_gt ht)]
    exact max_eq_right hnonneg
  change x + X.X t ω - barrierStrategy X x a t ω =
    a + X.X t ω - runningSup X t ω
  rw [hD, hraw]
  dsimp [S]
  ring
