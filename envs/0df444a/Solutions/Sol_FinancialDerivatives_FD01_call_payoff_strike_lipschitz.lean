-- Prove2me | solution 1 for FinancialDerivatives.FD01.call_payoff_strike_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:04.834633+00:00
-- url     : https://prove2.me/submissions/bc0779e8-1de0-4e2e-b64b-2561c03f4e2f

import Mathlib



open Finset

theorem solution (s K₁ K₂ : ℝ) :
  |max (s - K₁) 0 - max (s - K₂) 0| ≤ |K₁ - K₂| := by
  rw [abs_le]; constructor <;> cases' le_total (s - K₁) 0 with h h <;> cases' le_total (s - K₂) 0 with h' h' <;>
    simp_all [max_eq_left, max_eq_right] <;> cases' abs_cases (K₁ - K₂) with a a <;> linarith
