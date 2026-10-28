-- Prove2me | solution 1 for FinancialDerivatives.FD03.upWeight_stock_martingale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:11:30.64998+00:00
-- url     : https://prove2.me/submissions/ef53fb2b-5cc0-46c1-aa9e-dc3bb5c108dd

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_upWeight
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket) :
    upWeight m * m.up + (1 - upWeight m) * m.down =
      m.growth := by
  have hud : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
  have hg : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
  unfold upWeight
  field_simp
  ring


