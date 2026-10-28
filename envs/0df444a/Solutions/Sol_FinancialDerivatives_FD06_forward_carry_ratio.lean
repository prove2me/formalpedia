-- Prove2me | solution 1 for FinancialDerivatives.FD06.forward_carry_ratio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:05:18.742892+00:00
-- url     : https://prove2.me/submissions/ffb99005-5b8a-46ea-b1c6-98ef6911eca4

import Mathlib
import Definitions.Def_fd06_deterministicForward

open FinancialDerivatives.FD06

theorem solution (S R Q : ℝ) (hS : 0 < S) : deterministicForward S R Q = S * Real.exp R / Real.exp Q := by
  unfold deterministicForward; rw [Real.exp_sub]; ring
