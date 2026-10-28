-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_clock_weak_survival_past_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:25:04.461804+00:00
-- url     : https://prove2.me/submissions/e77ec896-bac3-4f2d-a8dc-b4f856c45ca4

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_lowerCrossingClock_lt_horizon_iff_exists_witness
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The lower-crossing clock survives to t iff all earlier states avoid crossing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ)
    (ω : Ω) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ twoSidedExitDownTime X lower ω ↔
      ∀ s : ℝ≥0, s < t → lower ≤ X.X s ω := by
  constructor
  · intro ht s hs
    by_contra hnot
    have hcross : X.X s ω < lower := lt_of_not_ge hnot
    have hclock : twoSidedExitDownTime X lower ω < (t : ℝ≥0∞) := by
      exact (lowerCrossingClock_lt_horizon_iff_exists_witness
        X lower ω t).2 ⟨s, hs, hcross⟩
    exact (not_lt_of_ge ht) hclock
  · intro h
    by_contra hnot
    have hclock : twoSidedExitDownTime X lower ω < (t : ℝ≥0∞) :=
      lt_of_not_ge hnot
    obtain ⟨s, hs, hcross⟩ :=
      (lowerCrossingClock_lt_horizon_iff_exists_witness X lower ω t).1 hclock
    exact (not_lt_of_ge (h s hs)) hcross
