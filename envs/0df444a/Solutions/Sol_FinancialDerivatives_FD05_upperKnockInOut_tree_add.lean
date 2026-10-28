-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperKnockInOut_tree_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:40:50.127671+00:00
-- url     : https://prove2.me/submissions/d344b47e-90a6-43a2-bb4c-4d4d74271eb5

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_payoffTreeZip
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_upperKnockInTree
import Definitions.Def_fd05_vanillaTerminalTree

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

theorem solution (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    payoffTreeZip (fun a b => a + b) N
      (upperKnockInTree m B monitor g N 0 m.initialSpot false)
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) =
    vanillaTerminalTree m N g := by
  simpa only [vanillaTerminalTree] using A3FD_tree_add m B monitor g N 0 m.initialSpot false
