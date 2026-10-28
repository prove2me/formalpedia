-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_clock_strict_survival_closed_history_offclock_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:10:52.386905+00:00
-- url     : https://prove2.me/submissions/3fcba03a-6a0f-4e0e-bbc3-9bbdba0bcb1f

import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_clock_weak_survival_past_ws01a
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Away from the exit instant, strict killing and closed-history killing agree. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hne : (t : ℝ≥0∞) ≠ twoSidedExitDownTime X lower ω) :
    (t : ℝ≥0∞) < twoSidedExitDownTime X lower ω ↔
      ∀ s : ℝ≥0, s ≤ t → lower ≤ X.X s ω := by
  constructor
  · intro hstop s hs
    by_contra hnot
    have hcross : X.X s ω < lower := lt_of_not_ge hnot
    have hclock : twoSidedExitDownTime X lower ω ≤ (s : ℝ≥0∞) := by
      simpa only [neg_neg] using
        (twoSidedExitDownTime_le_of_strict_lower_gap_observed
          X (-lower) ω s (by simpa only [neg_neg] using hcross))
    have hst : (s : ℝ≥0∞) ≤ (t : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hs
    exact (not_lt_of_ge (le_trans hclock hst)) hstop
  · intro hhistory
    have hweak : (t : ℝ≥0∞) ≤ twoSidedExitDownTime X lower ω :=
      (chat04_lower_clock_weak_survival_past_ws01a X lower ω t).2
        (by intro s hs; exact hhistory s (le_of_lt hs))
    exact lt_of_le_of_ne hweak hne
