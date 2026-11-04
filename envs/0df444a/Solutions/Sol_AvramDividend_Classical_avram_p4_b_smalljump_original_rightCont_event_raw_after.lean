-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_event_raw_after
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:11:15.426641+00:00
-- url     : https://prove2.me/submissions/3d9ddb04-542f-4ef8-81e5-253a16ecda84

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every event measurable at the actual source right-continuous time s
is measurable in the original raw sigma-algebra at each strictly later
time r. This is the filtration interface for the original jump rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {s r : ℝ≥0} (hsr : s < r)
    {A : Set Ω} (hA : MeasurableSet[𝓕.rightCont s] A) :
    MeasurableSet[𝓕 r] A := by
  have hle : 𝓕.rightCont s ≤ 𝓕 r := by
    rw [Filtration.rightCont_eq]
    exact iInf₂_le r hsr
  exact hle A hA
