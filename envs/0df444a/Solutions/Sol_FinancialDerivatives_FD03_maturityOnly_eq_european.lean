-- Prove2me | solution 1 for FinancialDerivatives.FD03.maturityOnly_eq_european
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:07:54.366577+00:00
-- url     : https://prove2.me/submissions/5b64f269-6779-46e2-bdc2-2ed362e59da6

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_snellValue
import Definitions.Def_fd03_exerciseStockTree
import Mathlib.Tactic
import Definitions.Def_fd03_oneStepValue
open FinancialDerivatives.FD03


open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (reward : ℝ → ℝ) :
    snellValue m n (exerciseStockTree m reward (fun _ => false) n spot) =
      europeanValue m n
        (payoffTreeMap reward n (terminalStockTree m n spot)) := by


  induction n generalizing spot with
  | zero => rfl
  | succ n ih =>
    show oneStepValue m _ _ = oneStepValue m _ _
    rw [ih, ih]
