-- Prove2me | solution 1 for FinancialDerivatives.FD05.emptyMonitoring_eq_vanilla
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:41:18.957885+00:00
-- url     : https://prove2.me/submissions/2149a3cc-73b9-4861-97cc-421105f19e34

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_vanillaTerminalTree
import Definitions.Def_fd03_europeanValue

open FinancialDerivatives.FD03 FinancialDerivatives.FD05


theorem A3FD_empty (m : BinomialMarket) (B : ℝ) (g : ℝ → ℝ) :
    ∀ (n t : ℕ) (S : ℝ),
    upperKnockOutTree m B (fun _ => false) g n t S false =
      payoffTreeMap g n (terminalStockTree m n S) := by
  intro n
  induction n with
  | zero => intro t S; simp [upperKnockOutTree, upperTouch, terminalStockTree, payoffTreeMap]
  | succ n ih =>
    intro t S
    have : (false || upperTouch B S (fun _ => false) t) = false := by simp [upperTouch]
    simp only [upperKnockOutTree, terminalStockTree, payoffTreeMap, this, ih]

theorem solution (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (g : ℝ → ℝ) :
    europeanValue m N
      (upperKnockOutTree m B (fun _ => false) g N 0 m.initialSpot false) =
    europeanValue m N (vanillaTerminalTree m N g) := by
  rw [A3FD_empty]
  rfl
