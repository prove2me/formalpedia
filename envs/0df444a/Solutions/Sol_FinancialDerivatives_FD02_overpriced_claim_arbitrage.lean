-- Prove2me | solution 1 for FinancialDerivatives.FD02.overpriced_claim_arbitrage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:16:15.473838+00:00
-- url     : https://prove2.me/submissions/fb12d356-8807-4432-9bd0-d54afeb6390f

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

theorem solution (m : TwoStateMarket) (H : Bool → ℝ) (p : ℝ) (hp : riskNeutralValue m H < p) :
  ¬ ClaimNoArbitrage m H p := by
  intro hC
  have hg := m.growth_pos
  set r := replicatingTrade m H
  have hp1 := rep_pay m H true
  have hp0 := rep_pay m H false
  have hc := rep_cost m H
  obtain ⟨h1, -⟩ := hC ⟨r.shares, r.cash + (p - riskNeutralValue m H)⟩ (-1)
    (by simp only [initialCost] at hc ⊢; linarith)
    (by simp only [terminalPayoff] at hp1 ⊢; nlinarith)
    (by simp only [terminalPayoff] at hp0 ⊢; nlinarith)
  simp only [terminalPayoff] at hp1 h1
  nlinarith
