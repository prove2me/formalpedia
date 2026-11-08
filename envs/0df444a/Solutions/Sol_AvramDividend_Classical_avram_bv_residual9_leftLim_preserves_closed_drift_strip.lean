-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_leftLim_preserves_closed_drift_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:41:11.596702+00:00
-- url     : https://prove2.me/submissions/72d28f03-25b2-4dca-b4b3-2c67092a6949

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- The literal left-limit of a bounded original reserve remains in the closed drift strip. -/
theorem solution
    (f : ℝ≥0 → ℝ) (a : ℝ≥0) (L U : ℝ)
    (hf : ∀ t : ℝ≥0, t ≤ a → L ≤ f t ∧ f t ≤ U) :
    L ≤ Function.leftLim f a ∧ Function.leftLim f a ≤ U := by
  have hmem : ∀ᶠ t in 𝓝[≤] a, f t ∈ Icc L U := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hf t ht
  exact isClosed_Icc.mem_of_mapClusterPt (mapClusterPt_leftLim f a) hmem
