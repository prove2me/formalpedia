-- Prove2me | solution 1 for CountingLLL.ContractedWalk.weighted_cost_finite
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:03:06.03189+00:00
-- url     : https://prove2.me/submissions/f5aba862-e24b-406f-981e-5d1007167ae0

import Definitions.Def_CountingLLL_ContractedCost
import Theorems.Thm_CountingLLL_ContractedWalk_absorption_and_expected_changes
set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal

private theorem weight_le_active (ω : Tape) (i j t : ℕ) (hj : 1 ≤ j) :
    changeWeight ω i j t ≤ (if level ω i t = 0 then 0 else 1) := by
  unfold changeWeight
  split_ifs with hz
  · rfl
  · apply ENNReal.inv_le_one.mpr
    have hn : 1 ≤ j + upwardBefore ω i t := by omega
    exact_mod_cast hn

private theorem weighted_le_changes (ω : Tape) (i j : ℕ) (hj : 1 ≤ j) :
    weightedChanges ω i j ≤ changes ω i := by
  unfold weightedChanges changes
  exact ENNReal.tsum_le_tsum (fun t => weight_le_active ω i j t hj)

/-- The weighted-change expectation is bounded by the expected change count. -/
theorem solution (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1/3) (i j : ℕ) (hj : 1 ≤ j) :
    expectedWeightedChanges (ENNReal.ofReal θ) i j ≤ ENNReal.ofReal ((i : ℝ)/(1-3*θ)) := by
  calc
    expectedWeightedChanges (ENNReal.ofReal θ) i j ≤ expectedChanges (ENNReal.ofReal θ) i := by
      unfold expectedWeightedChanges expectedChanges
      exact lintegral_mono (fun ω => weighted_le_changes ω i j hj)
    _ ≤ _ := (absorption_and_expected_changes θ hθ0 hθ1 i).2
