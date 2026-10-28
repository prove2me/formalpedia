-- Prove2me | solution 1 for FinancialDerivatives.FD03.terminalStockTree_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:05:44.076415+00:00
-- url     : https://prove2.me/submissions/22ca30ab-e88c-4425-a456-b7b6e97dcae1

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd03_payoffTreeAll
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot) :
    payoffTreeAll (fun x => 0 < x) n
      (terminalStockTree m n spot) := by
  induction n generalizing spot with
  | zero => exact hspot
  | succ n ih =>
    exact ⟨ih _ (mul_pos hspot (by linarith [m.down_pos, m.down_lt_growth, m.growth_lt_up])),
      ih _ (mul_pos hspot m.down_pos)⟩


