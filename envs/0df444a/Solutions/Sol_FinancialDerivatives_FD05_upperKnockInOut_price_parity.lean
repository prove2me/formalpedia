-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperKnockInOut_price_parity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:40:52.576773+00:00
-- url     : https://prove2.me/submissions/b938164f-6e35-4b7f-83ec-3b09c9388ad3

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_upperKnockInTree
import Definitions.Def_fd05_vanillaTerminalTree
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeZip
import Theorems.Thm_FinancialDerivatives_FD03_european_add

open FinancialDerivatives.FD03 FinancialDerivatives.FD05


theorem A3FD_tree_add (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    ∀ (n t : ℕ) (S : ℝ) (hit : Bool),
    payoffTreeZip (fun a b => a + b) n
      (upperKnockInTree m B monitor g n t S hit)
      (upperKnockOutTree m B monitor g n t S hit) =
    payoffTreeMap g n (terminalStockTree m n S) := by
  intro n
  induction n with
  | zero =>
    intro t S hit
    simp only [upperKnockInTree, upperKnockOutTree, payoffTreeZip, terminalStockTree, payoffTreeMap]
    split_ifs <;> simp
  | succ n ih =>
    intro t S hit
    simp only [upperKnockInTree, upperKnockOutTree, payoffTreeZip, terminalStockTree, payoffTreeMap, ih]

theorem solution (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    europeanValue m N
      (upperKnockInTree m B monitor g N 0 m.initialSpot false) +
    europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) =
    europeanValue m N (vanillaTerminalTree m N g) := by
  rw [← FinancialDerivatives.FD03.european_add, A3FD_tree_add]
  rfl
