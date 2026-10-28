-- Prove2me | solution 1 for FinancialDerivatives.FD01.put_payoff_antitone_spot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:06:58.48198+00:00
-- url     : https://prove2.me/submissions/fbb63fce-79b8-4fbf-9408-75c0089206e8

import Mathlib



open Finset

theorem solution (s₁ s₂ K : ℝ) (hs : s₁ ≤ s₂) :
  max (K - s₂) 0 ≤ max (K - s₁) 0 := max_le_max (by linarith) le_rfl
