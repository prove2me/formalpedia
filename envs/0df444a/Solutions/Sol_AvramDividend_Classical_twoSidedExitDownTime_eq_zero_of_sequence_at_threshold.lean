-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitDownTime_eq_zero_of_sequence_at_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:26:37.243272+00:00
-- url     : https://prove2.me/submissions/6eaf8ef5-da6f-408c-b162-7b1ddd24daf2

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Strict crossings along times approaching zero force passage time zero at any level. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω)
    (s : ℕ → ℝ≥0)
    (hs : Tendsto s atTop (nhds 0))
    (hcross : ∀ n : ℕ, X.X (s n) ω < b) :
    twoSidedExitDownTime X b ω = 0 := by
  have h : ∀ n, twoSidedExitDownTime X b ω ≤ (s n : ℝ≥0∞) := by
    intro n
    have hobs := twoSidedExitDownTime_le_of_strict_lower_gap_observed X (-b) ω (s n)
      (by simpa using hcross n)
    simpa only [neg_neg] using hobs
  have hs' : Tendsto (fun n => (s n : ℝ≥0∞)) atTop (nhds 0) := by
    have hc := (ENNReal.continuous_coe.tendsto 0).comp hs
    simpa [Function.comp_def] using hc
  exact le_antisymm (ge_of_tendsto' hs' h) zero_le
