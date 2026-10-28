-- Prove2me | solution 1 for FinancialDerivatives.FD05.barrier_claim_unique_no_arbitrage_price
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:44:11.781469+00:00
-- url     : https://prove2.me/submissions/dc092025-2053-459d-9e45-4f8a8f7c1924

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_quotedClaimArbitrage
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_discountedSurvivalPathPrice
import Definitions.Def_fd03_europeanValue
import Theorems.Thm_FinancialDerivatives_FD03_quotedClaim_noArbitrage_iff_value
import Theorems.Thm_FinancialDerivatives_FD05_upperKnockOut_eq_path_sum

open FinancialDerivatives.FD03 FinancialDerivatives.FD05

theorem solution (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (monitor : ℕ → Bool)
    (g : ℝ → ℝ) (quote : ℝ) :
    ¬ quotedClaimArbitrage m N m.initialSpot
        (upperKnockOutTree m B monitor g N 0 m.initialSpot false) quote ↔
      quote = discountedSurvivalPathPrice m N B monitor g := by
  rw [← FinancialDerivatives.FD05.upperKnockOut_eq_path_sum]
  exact FinancialDerivatives.FD03.quotedClaim_noArbitrage_iff_value m N _ m.initialSpot_pos _ _
