-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys105_compound_poisson_threshold_reward_HJB_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:03:35.679375+00:00
-- url     : https://prove2.me/submissions/5b6fe60e-2182-44e3-8316-d9c9734094cf

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The piecewise-linear reward with a jump at ruin satisfies the
interior generator inequality for drift 10, rate 20, marks -1, q = 1. -/
theorem solution (y : ℝ) (hy : 0 < y) :
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else 1 + z
    10 + 20 * (w (y - 1) - w y) - w y ≤ 0 := by
  dsimp
  have hnonneg : ¬ y < 0 := not_lt.mpr (le_of_lt hy)
  by_cases hcontact : y < 1
  · have hbelow : y - 1 < 0 := by linarith
    simp only [if_pos hbelow, if_neg hnonneg]
    linarith
  · have habove : ¬ y - 1 < 0 := by linarith
    simp only [if_neg habove, if_neg hnonneg]
    linarith
