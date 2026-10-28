-- Prove2me | solution 1 for AvramDividend.Classical.killed_higherRecord_survival_implies_lowerRecord_survival_with_measure_import
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:00:00.046366+00:00
-- url     : https://prove2.me/submissions/709af05c-a331-4331-85c2-bce1fe1fc8cd

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-! Surviving a later record entails survival of each earlier level. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b ε : ℝ)
    (hε : 0 ≤ ε) (ω : Ω)
    (hHigher : twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω) :
    twoSidedExitUpTime X b ω < barrierRuinTime X a ω := by
  exact lt_of_le_of_lt
    (twoSidedExitUpTime_mono_threshold
      X b (b + ε) (le_add_of_nonneg_right hε) ω)
    hHigher