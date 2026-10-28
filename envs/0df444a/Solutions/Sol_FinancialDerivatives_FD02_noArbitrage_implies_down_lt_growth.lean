-- Prove2me | solution 1 for FinancialDerivatives.FD02.noArbitrage_implies_down_lt_growth
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:58:20.417721+00:00
-- url     : https://prove2.me/submissions/e30ab6fb-b72f-4789-aff1-7f2c1566572d

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_NoArbitrage
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (hNA : NoArbitrage m) :
  m.down < m.growth := by
  by_contra hc
  push_neg at hc
  have hs := m.spot_pos
  have hdu := m.down_lt_up
  obtain ⟨h1, -⟩ := hNA ⟨1, -m.spot⟩ (by simp [initialCost])
    (by simp only [terminalPayoff]; nlinarith) (by simp only [terminalPayoff]; nlinarith)
  simp only [terminalPayoff] at h1
  nlinarith
