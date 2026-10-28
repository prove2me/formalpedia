-- Prove2me | solution 1 for FinancialDerivatives.FD02.replicatingTrade_up
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:12:48.283487+00:00
-- url     : https://prove2.me/submissions/40217abf-2af5-4109-bdf6-c2d680854b0c

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_Replicates
import Definitions.Def_fd02_replicatingTrade
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (H : Bool → ℝ) :
  terminalPayoff m (replicatingTrade m H) true = H true := by
  have hs := m.spot_pos
  have hg := m.growth_pos
  have h : m.up - m.down ≠ 0 := by linarith [m.down_lt_up]
  simp only [terminalPayoff, replicatingTrade]
  field_simp
  ring
