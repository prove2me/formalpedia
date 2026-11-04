-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_strict_left_limit_at_zero_is_vacuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:59:53.568192+00:00
-- url     : https://prove2.me/submissions/38506c7b-0083-4031-87d6-3396836f7bb6

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- There are no nonnegative times strictly before the initial time.
Consequently the strict-left convergence condition at zero is automatic. -/
theorem solution (Y : ℝ≥0 → ℝ) :
    Tendsto Y (𝓝[<] (0 : ℝ≥0))
      (𝓝 (Function.leftLim Y 0)) := by
  have hempty : Set.Iio (0 : ℝ≥0) = ∅ := by
    ext t
    simp
  have hbot : (𝓝[<] (0 : ℝ≥0)) = (⊥ : Filter ℝ≥0) := by
    simpa only [hempty] using (nhdsWithin_empty (0 : ℝ≥0))
  rw [hbot]
  exact tendsto_bot
