-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_continuous_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:22:50.955477+00:00
-- url     : https://prove2.me/submissions/ef052fe5-6832-4eac-ad9c-f5a95ec02fdd

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_test_weighted_log_vanishes_near_one
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_test_weighted_log_vanishes_near_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    ContinuousOn (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) (Ici 0) := by
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    have hfzero : f 0 = 0 := hfupper 0 (by linarith)
    have heq :=
      AvramDividend.Classical.avram_p2_b_rate_negative_test_weighted_log_vanishes_near_zero
        f a hflower hfzero
    exact (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Ici 0) 0).congr_of_eventuallyEq heq (by simp [hfzero])
  by_cases hz1 : z = 1
  · subst z
    have heq :=
      AvramDividend.Classical.avram_p2_b_rate_negative_test_weighted_log_vanishes_near_one
        f ε hε hfupper
    have heq' := heq.filter_mono (nhdsWithin_le_nhds : nhdsWithin (1 : ℝ) (Ici 0) ≤ nhds (1 : ℝ))
    have hfzero : f 0 = 0 := hfupper 0 (by linarith)
    exact (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Ici 0) 1).congr_of_eventuallyEq heq' (by simp [hfzero])
  have hnum : ContinuousAt (fun w : ℝ => f (Real.log w)) z :=
    hf.continuousAt.comp (Real.continuousAt_log hz0)
  have hden : ContinuousAt (fun w : ℝ => (w - 1) ^ 4) z :=
    (continuousAt_id.sub continuousAt_const).pow 4
  have hden_ne : (z - 1) ^ 4 ≠ 0 := pow_ne_zero 4 (sub_ne_zero.mpr hz1)
  exact (hnum.div hden hden_ne).continuousWithinAt
