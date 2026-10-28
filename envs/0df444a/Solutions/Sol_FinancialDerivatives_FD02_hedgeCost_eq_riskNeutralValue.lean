-- Prove2me | solution 1 for FinancialDerivatives.FD02.hedgeCost_eq_riskNeutralValue
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:14:02.351491+00:00
-- url     : https://prove2.me/submissions/602750a3-3f40-4c54-9b8c-72d80e703728

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_Replicates
import Definitions.Def_fd02_replicatingTrade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_riskNeutralValue
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (H : Bool → ℝ) :
  initialCost m (replicatingTrade m H) = riskNeutralValue m H := by
  have hs := m.spot_pos
  have hg := m.growth_pos
  have h : m.up - m.down ≠ 0 := by linarith [m.down_lt_up]
  simp only [initialCost, replicatingTrade, riskNeutralValue, riskNeutralUp]
  field_simp
  ring
