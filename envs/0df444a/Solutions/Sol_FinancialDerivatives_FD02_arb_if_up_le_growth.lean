-- Prove2me | solution 1 for FinancialDerivatives.FD02.arb_if_up_le_growth
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:58:20.46123+00:00
-- url     : https://prove2.me/submissions/69b9f738-eada-4f96-956c-112ae38da97d

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_NoArbitrage
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (h : m.up ≤ m.growth) :
  ¬ NoArbitrage m := by
  intro hNA
  have hs := m.spot_pos
  have hdu := m.down_lt_up
  obtain ⟨-, h2⟩ := hNA ⟨-1, m.spot⟩ (by simp [initialCost])
    (by simp only [terminalPayoff]; nlinarith) (by simp only [terminalPayoff]; nlinarith)
  simp only [terminalPayoff] at h2
  nlinarith
