-- Prove2me | solution 2 for AvramDividend.Classical.killed_higherRecord_survival_implies_lowerRecord_survival_with_measure_import
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:00:11.730815+00:00
-- url     : https://prove2.me/submissions/e84c0daf-0432-4379-b203-68434c2ed4eb

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b ε : ℝ)
    (hε : 0 ≤ ε) (ω : Ω)
    (hHigher : twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω) :
    twoSidedExitUpTime X b ω < barrierRuinTime X a ω := by 
  exact lt_of_le_of_lt (twoSidedExitUpTime_mono_threshold X b (b + ε) (by linarith) ω) hHigher
