-- Prove2me | solution 1 for FinancialDerivatives.FD02.replicatingTrade_down
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:12:48.127741+00:00
-- url     : https://prove2.me/submissions/23bad553-823c-4b22-9f1f-5316e40c3878

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_Replicates
import Definitions.Def_fd02_replicatingTrade
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (H : Bool → ℝ) :
  terminalPayoff m (replicatingTrade m H) false = H false := by
  have hs := m.spot_pos
  have hg := m.growth_pos
  have h : m.up - m.down ≠ 0 := by linarith [m.down_lt_up]
  simp only [terminalPayoff, replicatingTrade]
  field_simp
  ring
