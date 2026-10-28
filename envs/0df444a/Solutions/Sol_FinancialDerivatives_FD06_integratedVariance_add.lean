-- Prove2me | solution 1 for FinancialDerivatives.FD06.integratedVariance_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:09:16.868168+00:00
-- url     : https://prove2.me/submissions/d0e3fc6f-8b04-41e7-abf7-001008c07deb

import Mathlib
import Definitions.Def_fd06_integratedVariance

open FinancialDerivatives.FD06

theorem solution (σ : ℝ → ℝ) (t u T : ℝ) (hσ : Continuous σ) : integratedVariance σ t T = integratedVariance σ t u + integratedVariance σ u T := by
  unfold integratedVariance
  rw [intervalIntegral.integral_add_adjacent_intervals] <;> exact (hσ.pow 2).intervalIntegrable _ _
