-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperKnockOutTree_le_vanilla
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:40:57.766723+00:00
-- url     : https://prove2.me/submissions/e0cb3256-2771-461b-a7d8-f790fcd62602

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_payoffTreeLe
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_vanillaTerminalTree

open FinancialDerivatives.FD03 FinancialDerivatives.FD05


theorem A3FD_le_vanilla (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hg : ∀ S : ℝ, 0 ≤ g S) :
    ∀ (n t : ℕ) (S : ℝ) (hit : Bool),
    payoffTreeLe n (upperKnockOutTree m B monitor g n t S hit)
      (payoffTreeMap g n (terminalStockTree m n S)) := by
  intro n
  induction n with
  | zero =>
    intro t S hit
    simp only [upperKnockOutTree, terminalStockTree, payoffTreeMap, payoffTreeLe]
    split_ifs
    · exact hg S
    · exact le_rfl
  | succ n ih =>
    intro t S hit
    simp only [upperKnockOutTree, terminalStockTree, payoffTreeMap, payoffTreeLe]
    exact ⟨ih _ _ _, ih _ _ _⟩

theorem solution (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hg : ∀ S : ℝ, 0 ≤ g S) :
    payoffTreeLe N (upperKnockOutTree m B monitor g N 0 m.initialSpot false) (vanillaTerminalTree m N g) := by
  simpa only [vanillaTerminalTree] using A3FD_le_vanilla m B monitor g hg N 0 m.initialSpot false
