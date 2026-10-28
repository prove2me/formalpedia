-- Prove2me | solution 1 for AvramDividend.Classical.barrierRuinTime_zero_of_near_zero_path_decrease
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:32:52.041393+00:00
-- url     : https://prove2.me/submissions/823b8fcd-8d23-4771-b6fc-365abda233c6

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_drawdown
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Local path decreases imply instantaneous zero-barrier reflected ruin,
even when the path never crosses below its initial level. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDecrease : ∀ ε : ℝ≥0, 0 < ε →
      ∃ s t : ℝ≥0, s ≤ t ∧ t < ε ∧ X.X t ω < X.X s ω) :
    barrierRuinTime X 0 ω = 0 := by
  obtain ⟨hmon, hpath⟩ := runningSup_monotone_and_path_le X ω
  apply barrierRuinTime_zero_of_near_zero_drawdown X 0 ω
  intro ε hε
  obtain ⟨s, t, hst, htε, hdrop⟩ := hDecrease ε hε
  refine ⟨t, htε, ?_⟩
  change 0 < runningSup X t ω - X.X t ω
  have hbound : X.X s ω ≤ runningSup X t ω :=
    (hpath s).trans (hmon hst)
  exact sub_pos.mpr (lt_of_lt_of_le hdrop hbound)
