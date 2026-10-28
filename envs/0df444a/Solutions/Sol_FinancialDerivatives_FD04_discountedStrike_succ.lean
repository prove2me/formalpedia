-- Prove2me | solution 1 for FinancialDerivatives.FD04.discountedStrike_succ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:53:14.678986+00:00
-- url     : https://prove2.me/submissions/192cec80-c2eb-43cc-8b5d-d809df646101

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_discountedStrike
open FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket)
    (K : ℝ) (n : ℕ) :
    discountedStrike m K (n + 1) =
      discountedStrike m K n / m.growth := by
  unfold discountedStrike; rw [pow_succ, div_div]


