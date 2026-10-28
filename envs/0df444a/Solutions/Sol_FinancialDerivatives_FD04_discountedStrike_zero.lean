-- Prove2me | solution 1 for FinancialDerivatives.FD04.discountedStrike_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:53:11.310573+00:00
-- url     : https://prove2.me/submissions/b6d38d52-d7d4-481f-a752-9cba0df5c807

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_discountedStrike
open FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (K : ℝ) :
    discountedStrike m K 0 = K := by
  unfold discountedStrike; simp


