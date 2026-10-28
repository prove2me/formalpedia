-- Prove2me | solution 1 for FinancialDerivatives.FD02.replicationCost_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:15:28.446471+00:00
-- url     : https://prove2.me/submissions/0b6b6e15-27a5-464d-a82b-548d890e1e74

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

theorem solution (m : TwoStateMarket) (H : Bool → ℝ) (t : Trade) (ht : Replicates m t H) :
  initialCost m t = riskNeutralValue m H := by
  have hg := m.growth_pos
  have h : m.up - m.down ≠ 0 := by linarith [m.down_lt_up]
  simp only [riskNeutralValue, ← ht true, ← ht false, terminalPayoff, initialCost, riskNeutralUp]
  field_simp
  ring
