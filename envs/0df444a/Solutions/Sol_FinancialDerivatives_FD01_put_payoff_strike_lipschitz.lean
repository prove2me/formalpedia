-- Prove2me | solution 1 for FinancialDerivatives.FD01.put_payoff_strike_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:06:57.462988+00:00
-- url     : https://prove2.me/submissions/50f72953-7325-47aa-b704-3edbecf8ee34

import Mathlib



open Finset

theorem solution (s K₁ K₂ : ℝ) :
  |max (K₁ - s) 0 - max (K₂ - s) 0| ≤ |K₁ - K₂| := by
  rw [abs_le]; constructor <;> cases' le_total (K₁ - s) 0 with h h <;> cases' le_total (K₂ - s) 0 with h' h' <;>
    simp_all [max_eq_left, max_eq_right] <;> cases' abs_cases (K₁ - K₂) with a a <;> linarith
