-- Prove2me | solution 1 for FinancialDerivatives.FD06.discounted_call_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:04:31.750329+00:00
-- url     : https://prove2.me/submissions/18796485-df90-45fa-9601-3415160f01f5

import Mathlib
import Definitions.Def_fd06_discountedCallGaussian

open FinancialDerivatives.FD06

theorem solution (S K R Q V : ℝ) : 0 ≤ discountedCallGaussian S K R Q V := by
  unfold discountedCallGaussian; exact mul_nonneg (Real.exp_pos _).le (MeasureTheory.integral_nonneg fun _ => le_max_right _ _)
