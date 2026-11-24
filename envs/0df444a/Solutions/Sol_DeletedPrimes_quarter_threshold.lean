-- Prove2me | solution 1 for DeletedPrimes.quarter_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:18:45.526918+00:00
-- url     : https://prove2.me/submissions/97d4bfe7-7076-47b0-9e22-505c7e53376d

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
import Theorems.Thm_DeletedPrimes_isRegular_empty
import Theorems.Thm_DeletedPrimes_isRegular_of_theta_lt


set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution (ZeroRight : Set ℕ → Prop)
    (hnotRH : ¬ RiemannHypothesis → ZeroRight ∅)
    (hRH : RiemannHypothesis → ∀ α : ℝ, 1 / 2 < α → α < 1 → ∃ S : Set ℕ, theta S = α / 2 ∧ ZeroRight S) :
    ∀ θ : ℝ, 1 / 4 < θ → ∃ S : Set ℕ, IsRegular S θ ∧ ZeroRight S := by
  intro θ hθ
  by_cases hR : RiemannHypothesis
  · set m := min 1 (2 * θ) with hm
    have hm1 : m ≤ 1 := min_le_left _ _
    have hm2 : m ≤ 2 * θ := min_le_right _ _
    have hm3 : 1 / 2 < m := lt_min (by norm_num) (by linarith)
    obtain ⟨S, hS, hZ⟩ := hRH hR ((1 / 2 + m) / 2) (by linarith) (by linarith)
    refine ⟨S, isRegular_of_theta_lt ?_, hZ⟩
    rw [hS]; linarith
  · exact ⟨∅, isRegular_empty (by linarith), hnotRH hR⟩
end DeletedPrimes
