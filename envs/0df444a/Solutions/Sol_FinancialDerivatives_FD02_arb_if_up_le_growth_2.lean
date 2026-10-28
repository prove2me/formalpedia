-- Prove2me | solution 2 for FinancialDerivatives.FD02.arb_if_up_le_growth
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:58:36.02198+00:00
-- url     : https://prove2.me/submissions/37eb58a1-0247-40ba-9bd6-79060c650476

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_NoArbitrage
open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (h : m.up ≤ m.growth) :
  ¬ NoArbitrage m := by
  intro hna
  have hs := m.spot_pos
  have hdu := m.down_lt_up
  have := hna ⟨-1, m.spot⟩ (by simp [initialCost]) (by simp [terminalPayoff]; nlinarith)
    (by simp [terminalPayoff]; nlinarith)
  simp [terminalPayoff] at this
  nlinarith [this.2]
