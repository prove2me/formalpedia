-- Prove2me | solution 1 for FinancialDerivatives.FD01.call_payoff_monotone_spot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:06:59.47921+00:00
-- url     : https://prove2.me/submissions/32c0a8da-fc91-4aea-8e66-759925e5a35b

import Mathlib



open Finset

theorem solution (s₁ s₂ K : ℝ) (hs : s₁ ≤ s₂) :
  max (s₁ - K) 0 ≤ max (s₂ - K) 0 := max_le_max (by linarith) le_rfl
