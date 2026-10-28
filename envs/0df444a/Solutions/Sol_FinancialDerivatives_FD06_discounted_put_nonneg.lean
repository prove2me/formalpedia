-- Prove2me | solution 1 for FinancialDerivatives.FD06.discounted_put_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:08:12.89866+00:00
-- url     : https://prove2.me/submissions/1c5fa501-df83-4755-87c0-8db255bb7c76

import Mathlib
import Definitions.Def_fd06_discountedPutGaussian

open FinancialDerivatives.FD06

theorem solution (S K R Q V : ℝ) : 0 ≤ discountedPutGaussian S K R Q V := by
  unfold discountedPutGaussian; exact mul_nonneg (Real.exp_pos _).le (MeasureTheory.integral_nonneg fun _ => le_max_right _ _)
