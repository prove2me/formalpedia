-- Prove2me | solution 1 for FinancialDerivatives.FD06.integratedRate_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:08:28.838234+00:00
-- url     : https://prove2.me/submissions/3c1ffaae-3946-46cc-a3cf-05604d0232ed

import Mathlib
import Definitions.Def_fd06_integratedRate

open FinancialDerivatives.FD06

theorem solution (r : ℝ → ℝ) (t u T : ℝ) (hr : Continuous r) : integratedRate r t T = integratedRate r t u + integratedRate r u T := by
  unfold integratedRate
  rw [intervalIntegral.integral_add_adjacent_intervals] <;> exact hr.intervalIntegrable _ _
