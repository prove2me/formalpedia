-- Prove2me | solution 1 for FinancialDerivatives.FD03.stock_terminal_pricing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:11:37.298048+00:00
-- url     : https://prove2.me/submissions/af3ee465-96c0-49dc-a220-1ed6f08f766f

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_terminalStockTree
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket) (n : ℕ)
    (spot : ℝ) :
    europeanValue m n (terminalStockTree m n spot) = spot := by
  have hud : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
  have hg : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
  induction n generalizing spot with
  | zero => rfl
  | succ n ih =>
    show oneStepValue m _ _ = _
    rw [ih, ih]
    unfold oneStepValue upWeight
    field_simp
    ring


