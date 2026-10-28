-- Prove2me | solution 1 for FinancialDerivatives.FD01.call_payoff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:10.804969+00:00
-- url     : https://prove2.me/submissions/ff6972d4-790d-440b-ad6b-97be1adf6597

import Mathlib



open Finset

theorem solution (s K : ℝ) (hs : 0 ≤ s) (hK : 0 ≤ K) :
  0 ≤ max (s - K) 0 ∧ max (s - K) 0 ≤ s := ⟨le_max_right _ _, max_le (by linarith) hs⟩
