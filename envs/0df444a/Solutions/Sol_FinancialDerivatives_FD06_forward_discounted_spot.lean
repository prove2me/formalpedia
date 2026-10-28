-- Prove2me | solution 1 for FinancialDerivatives.FD06.forward_discounted_spot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:05:35.135149+00:00
-- url     : https://prove2.me/submissions/b10e1c47-6ce9-4d84-a06b-18cbf50fe669

import Mathlib
import Definitions.Def_fd06_deterministicForward

open FinancialDerivatives.FD06

theorem solution (S R Q : ℝ) : Real.exp (-R) * deterministicForward S R Q = S * Real.exp (-Q) := by
  unfold deterministicForward; rw [mul_left_comm, ← Real.exp_add]; ring_nf
