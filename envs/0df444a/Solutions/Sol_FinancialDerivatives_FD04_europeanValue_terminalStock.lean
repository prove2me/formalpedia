-- Prove2me | solution 1 for FinancialDerivatives.FD04.europeanValue_terminalStock
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:53:01.149014+00:00
-- url     : https://prove2.me/submissions/18bab21a-adb3-4dea-a56e-16c04957711c

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_terminalStockTree
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) :
    europeanValue m n (terminalStockTree m n spot) = spot := by
  induction n generalizing spot with
  | zero => rfl
  | succ n ih =>
    simp only [terminalStockTree, europeanValue, ih]
    have h1 : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
    have h2 : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
    unfold oneStepValue upWeight
    field_simp
    ring


