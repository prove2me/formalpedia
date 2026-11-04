-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_compactly_supported_continuous_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:47:55.361902+00:00
-- url     : https://prove2.me/submissions/bffbe23c-0c93-4745-a98c-277e732b708a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_continuous_all_real
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_has_compact_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    ∃ g : CompactlySupportedContinuousMap ℝ ℝ,
      ∀ z : ℝ, g z = f (Real.log z) / (z - 1) ^ 4 := by
  let u : ContinuousMap ℝ ℝ :=
    ⟨(fun z : ℝ => f (Real.log z) / (z - 1) ^ 4),
      AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_continuous_all_real
        f hf a ε hε hflower hfupper⟩
  have hs : HasCompactSupport (u : ℝ → ℝ) := by
    exact AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_has_compact_support
      f ε hε hfupper
  refine ⟨CompactlySupportedContinuousMap.mk u hs, ?_⟩
  intro z
  rfl
