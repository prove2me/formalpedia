-- Prove2me | solution 1 for FinancialDerivatives.FD02.arb_if_growth_le_down
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:57:41.931208+00:00
-- url     : https://prove2.me/submissions/ae7ccd79-a54c-41be-91cb-8d7dfdb51ad1

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_NoArbitrage
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (h : m.growth ≤ m.down) :
  ¬ NoArbitrage m := by
  intro hNA
  have hs := m.spot_pos
  have hdu := m.down_lt_up
  obtain ⟨h1, -⟩ := hNA ⟨1, -m.spot⟩ (by simp [initialCost])
    (by simp only [terminalPayoff]; nlinarith) (by simp only [terminalPayoff]; nlinarith)
  simp only [terminalPayoff] at h1
  nlinarith
