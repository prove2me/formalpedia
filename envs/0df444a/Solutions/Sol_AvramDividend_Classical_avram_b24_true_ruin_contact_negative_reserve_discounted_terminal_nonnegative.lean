-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_true_ruin_contact_negative_reserve_discounted_terminal_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:03:01.327188+00:00
-- url     : https://prove2.me/submissions/9b0cf459-f515-43fc-a7ce-399c3c76da00

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (q : ℝ) (t : ℝ≥0) (y : ℝ) (hy : y ≤ 0) :
    0 ≤ Real.exp (-(q * (t : ℝ))) * w y := by
  have hw : 0 ≤ w y := by
    by_cases hneg : y < 0
    · rw [hw_neg y hneg]
    · have hzero : y = 0 := le_antisymm hy (le_of_not_gt hneg)
      simpa [hzero] using hw0
  exact mul_nonneg (Real.exp_nonneg _) hw
