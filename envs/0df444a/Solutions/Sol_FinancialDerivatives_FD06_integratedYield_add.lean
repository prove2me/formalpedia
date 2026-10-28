-- Prove2me | solution 1 for FinancialDerivatives.FD06.integratedYield_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:10:05.1883+00:00
-- url     : https://prove2.me/submissions/ce89f2ac-b9d0-41aa-a222-4e7a8104fcac

import Mathlib
import Definitions.Def_fd06_integratedYield

open FinancialDerivatives.FD06

theorem solution (q : ℝ → ℝ) (t u T : ℝ) (hq : Continuous q) : integratedYield q t T = integratedYield q t u + integratedYield q u T := by
  unfold integratedYield
  rw [intervalIntegral.integral_add_adjacent_intervals] <;> exact hq.intervalIntegrable _ _
