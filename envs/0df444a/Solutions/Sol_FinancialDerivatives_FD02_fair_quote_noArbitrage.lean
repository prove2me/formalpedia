-- Prove2me | solution 1 for FinancialDerivatives.FD02.fair_quote_noArbitrage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:16:25.630398+00:00
-- url     : https://prove2.me/submissions/23ee5ddb-6089-4509-a23e-43225e69e712

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_Replicates
import Definitions.Def_fd02_replicatingTrade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_riskNeutralValue
import Definitions.Def_fd02_NoArbitrage
import Definitions.Def_fd02_ClaimNoArbitrage
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem rep_pay (m : TwoStateMarket) (H : Bool → ℝ) (ω : Bool) :
    terminalPayoff m (replicatingTrade m H) ω = H ω := by
  have hs := m.spot_pos
  have hg := m.growth_pos
  have h : m.up - m.down ≠ 0 := by linarith [m.down_lt_up]
  cases ω <;> simp only [terminalPayoff, replicatingTrade] <;> field_simp <;> ring

theorem rep_cost (m : TwoStateMarket) (H : Bool → ℝ) :
    initialCost m (replicatingTrade m H) = riskNeutralValue m H := by
  have hs := m.spot_pos
  have hg := m.growth_pos
  have h : m.up - m.down ≠ 0 := by linarith [m.down_lt_up]
  simp only [initialCost, replicatingTrade, riskNeutralValue, riskNeutralUp]
  field_simp
  ring

theorem solution (m : TwoStateMarket) (hNA : NoArbitrage m) (H : Bool → ℝ) :
  ClaimNoArbitrage m H (riskNeutralValue m H) := by
  intro t a hcost h1 h0
  have hp1 := rep_pay m H true
  have hp0 := rep_pay m H false
  have hc := rep_cost m H
  generalize replicatingTrade m H = r at hp1 hp0 hc
  have key := hNA ⟨t.shares + a * r.shares, t.cash + a * r.cash⟩
  simp only [initialCost, terminalPayoff] at key hp1 hp0 hc hcost h1 h0 ⊢
  have e1 : (t.shares + a * r.shares) * m.spot * m.up + (t.cash + a * r.cash) * m.growth =
      t.shares * m.spot * m.up + t.cash * m.growth + a * H true := by linear_combination a * hp1
  have e0 : (t.shares + a * r.shares) * m.spot * m.down + (t.cash + a * r.cash) * m.growth =
      t.shares * m.spot * m.down + t.cash * m.growth + a * H false := by linear_combination a * hp0
  have ec : (t.shares + a * r.shares) * m.spot + (t.cash + a * r.cash) = 0 := by
    linear_combination hcost + a * hc
  rw [e1, e0] at key
  exact key ec h1 h0
