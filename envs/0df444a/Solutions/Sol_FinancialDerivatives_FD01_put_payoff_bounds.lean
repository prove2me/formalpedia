-- Prove2me | solution 1 for FinancialDerivatives.FD01.put_payoff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:09.976328+00:00
-- url     : https://prove2.me/submissions/68c350ab-5de1-4d6e-91e3-a86c2510bcd9

import Mathlib



open Finset

theorem solution (s K : ℝ) (hs : 0 ≤ s) (hK : 0 ≤ K) :
  0 ≤ max (K - s) 0 ∧ max (K - s) 0 ≤ K := ⟨le_max_right _ _, max_le (by linarith) hK⟩
