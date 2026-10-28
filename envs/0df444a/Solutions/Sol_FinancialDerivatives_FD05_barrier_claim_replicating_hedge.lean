-- Prove2me | solution 1 for FinancialDerivatives.FD05.barrier_claim_replicating_hedge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:44:14.15232+00:00
-- url     : https://prove2.me/submissions/bc7efc6e-454c-474f-9ab4-48b10fb07213

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_HedgeTree
import Definitions.Def_fd03_SelfFinancing
import Definitions.Def_fd03_hedgeTerminalPays
import Definitions.Def_fd03_hedgeWealth
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_discountedSurvivalPathPrice
import Definitions.Def_fd03_europeanValue
import Theorems.Thm_FinancialDerivatives_FD03_recursiveHedge_exists
import Theorems.Thm_FinancialDerivatives_FD05_upperKnockOut_eq_path_sum

open FinancialDerivatives.FD03 FinancialDerivatives.FD05

theorem solution (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    ∃ hedge : HedgeTree N,
      SelfFinancing m N m.initialSpot hedge ∧
      hedgeTerminalPays N hedge (upperKnockOutTree m B monitor g N 0 m.initialSpot false) ∧
      hedgeWealth m N m.initialSpot hedge =
        discountedSurvivalPathPrice m N B monitor g := by
  rw [← FinancialDerivatives.FD05.upperKnockOut_eq_path_sum]
  exact FinancialDerivatives.FD03.recursiveHedge_exists m N _ m.initialSpot_pos _
