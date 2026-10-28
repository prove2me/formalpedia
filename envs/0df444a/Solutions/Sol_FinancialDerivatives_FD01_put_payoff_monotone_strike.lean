-- Prove2me | solution 1 for FinancialDerivatives.FD01.put_payoff_monotone_strike
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:00.256995+00:00
-- url     : https://prove2.me/submissions/c0e1c7bf-7ca5-4439-9a7c-688116e1765a

import Mathlib



open Finset

theorem solution (s K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  max (K₁ - s) 0 ≤ max (K₂ - s) 0 := max_le_max (by linarith) le_rfl
