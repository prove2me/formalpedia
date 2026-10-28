-- Prove2me | solution 1 for FinancialDerivatives.FD02.replicatingTrade_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:13:22.749758+00:00
-- url     : https://prove2.me/submissions/d080a860-cc07-41ec-aafa-eec7e2f9b171

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_Replicates
import Definitions.Def_fd02_replicatingTrade
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (H : Bool → ℝ) :
  Replicates m (replicatingTrade m H) H := by
  have hs := m.spot_pos
  have hg := m.growth_pos
  have h : m.up - m.down ≠ 0 := by linarith [m.down_lt_up]
  intro ω
  cases ω <;> simp only [terminalPayoff, replicatingTrade] <;> field_simp <;> ring
