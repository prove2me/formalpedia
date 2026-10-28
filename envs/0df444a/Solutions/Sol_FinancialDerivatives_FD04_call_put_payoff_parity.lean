-- Prove2me | solution 1 for FinancialDerivatives.FD04.call_put_payoff_parity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:53:08.038761+00:00
-- url     : https://prove2.me/submissions/2204a273-4486-4812-8f09-7e7362b50e04

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_callPayoff
import Definitions.Def_fd04_putPayoff
open FinancialDerivatives.FD04
theorem solution (K spot : ℝ) :
    callPayoff K spot - putPayoff K spot = spot - K := by
  unfold callPayoff putPayoff
  rcases le_total spot K with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring


