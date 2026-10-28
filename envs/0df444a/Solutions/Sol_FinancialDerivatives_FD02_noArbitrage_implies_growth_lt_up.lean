-- Prove2me | solution 1 for FinancialDerivatives.FD02.noArbitrage_implies_growth_lt_up
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:58:57.391846+00:00
-- url     : https://prove2.me/submissions/bd416f7d-6713-4afc-8917-63e0245b5358

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_NoArbitrage
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (hNA : NoArbitrage m) :
  m.growth < m.up := by
  by_contra hc
  push_neg at hc
  have hs := m.spot_pos
  have hdu := m.down_lt_up
  obtain ⟨-, h2⟩ := hNA ⟨-1, m.spot⟩ (by simp [initialCost])
    (by simp only [terminalPayoff]; nlinarith) (by simp only [terminalPayoff]; nlinarith)
  simp only [terminalPayoff] at h2
  nlinarith
