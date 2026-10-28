-- Prove2me | solution 1 for FinancialDerivatives.FD01.call_payoff_antitone_strike
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:09.134771+00:00
-- url     : https://prove2.me/submissions/2ce9ef9b-91e1-4856-9b8a-f2bfc2c3acec

import Mathlib



open Finset

theorem solution (s K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  max (s - K₂) 0 ≤ max (s - K₁) 0 := max_le_max (by linarith) le_rfl
