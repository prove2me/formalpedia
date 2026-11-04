-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_leftLim_origin_nnreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:41:45.193533+00:00
-- url     : https://prove2.me/submissions/871aecd8-7f7a-4ad9-a8ae-a94b0ca1ad97

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology
open scoped NNReal

/-- At the bottom of the nonnegative time line, the left-limit convention
coincides with the source value, so there is no time-zero jump. -/
theorem solution (Y : ℝ≥0 → ℝ) :
    Function.leftLim Y 0 = Y 0 := by
  have h : ContinuousWithinAt Y (Iic (0 : ℝ≥0)) 0 := by
    have hset : Iic (0 : ℝ≥0) = {0} := by
      ext t
      simp only [mem_Iic, mem_singleton_iff]
      exact ⟨fun ht => le_antisymm ht (show (0 : ℝ≥0) ≤ t from bot_le), fun ht => ht.le⟩
    rw [hset]
    exact continuousWithinAt_singleton
  exact h.leftLim_eq
