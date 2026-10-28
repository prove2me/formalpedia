-- Prove2me | solution 1 for FinancialDerivatives.FD02.unique_replication_noArbitrage_pricing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:18:06.301433+00:00
-- url     : https://prove2.me/submissions/b1de3d14-9a6e-4321-a471-4813ae0da43d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_riskNeutralValue
import Definitions.Def_fd02_toFD01PriceSystem
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_Replicates
import Definitions.Def_fd02_NoArbitrage
import Definitions.Def_fd02_ClaimNoArbitrage
import Mathlib.Tactic
import Definitions.Def_fd02_replicatingTrade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_Replicates

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

theorem na_bounds (m : TwoStateMarket) (hNA : NoArbitrage m) :
    m.down < m.growth ∧ m.growth < m.up := by
  have hs := m.spot_pos
  have hdu := m.down_lt_up
  constructor
  · by_contra hc
    push_neg at hc
    obtain ⟨h1, -⟩ := hNA ⟨1, -m.spot⟩ (by simp [initialCost])
      (by simp only [terminalPayoff]; nlinarith) (by simp only [terminalPayoff]; nlinarith)
    simp only [terminalPayoff] at h1
    nlinarith
  · by_contra hc
    push_neg at hc
    obtain ⟨-, h2⟩ := hNA ⟨-1, m.spot⟩ (by simp [initialCost])
      (by simp only [terminalPayoff]; nlinarith) (by simp only [terminalPayoff]; nlinarith)
    simp only [terminalPayoff] at h2
    nlinarith

theorem claimNA_imp (m : TwoStateMarket) (H : Bool → ℝ) (p : ℝ) (hC : ClaimNoArbitrage m H p) :
    p = riskNeutralValue m H := by
  have hg := m.growth_pos
  have hp1 := rep_pay m H true
  have hp0 := rep_pay m H false
  have hc := rep_cost m H
  generalize replicatingTrade m H = r at hp1 hp0 hc
  simp only [initialCost, terminalPayoff] at hp1 hp0 hc
  rcases lt_trichotomy p (riskNeutralValue m H) with hlt | heq | hgt
  · exfalso
    obtain ⟨h1, -⟩ := hC ⟨-r.shares, -r.cash + (riskNeutralValue m H - p)⟩ 1
      (by simp only [initialCost]; linarith)
      (by simp only [terminalPayoff]; nlinarith) (by simp only [terminalPayoff]; nlinarith)
    simp only [terminalPayoff] at h1
    nlinarith
  · exact heq
  · exfalso
    obtain ⟨h1, -⟩ := hC ⟨r.shares, r.cash + (p - riskNeutralValue m H)⟩ (-1)
      (by simp only [initialCost]; linarith)
      (by simp only [terminalPayoff]; nlinarith) (by simp only [terminalPayoff]; nlinarith)
    simp only [terminalPayoff] at h1
    nlinarith

theorem fair (m : TwoStateMarket) (hNA : NoArbitrage m) (H : Bool → ℝ) :
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

theorem claimNA_iff (m : TwoStateMarket) (hNA : NoArbitrage m) (H : Bool → ℝ) (p : ℝ) :
    ClaimNoArbitrage m H p ↔ p = riskNeutralValue m H :=
  ⟨claimNA_imp m H p, fun h => h ▸ fair m hNA H⟩

theorem q_bounds (m : TwoStateMarket) (hNA : NoArbitrage m) :
    0 < riskNeutralUp m ∧ riskNeutralUp m < 1 := by
  obtain ⟨hd, hu⟩ := na_bounds m hNA
  unfold riskNeutralUp
  exact ⟨div_pos (by linarith) (by linarith), by rw [div_lt_one (by linarith)]; linarith⟩

theorem price_eq (m : TwoStateMarket) (hq0 : 0 < riskNeutralUp m) (hq1 : riskNeutralUp m < 1)
    (H : Bool → ℝ) : (toFD01PriceSystem m hq0 hq1).price H = riskNeutralValue m H := by
  have hg := m.growth_pos
  simp only [FinancialDerivatives.FD01.FinitePriceSystem.price, toFD01PriceSystem, Fintype.sum_bool,
    riskNeutralValue]
  field_simp

theorem solution (m : TwoStateMarket) (hNA : NoArbitrage m) (H : Bool → ℝ) :
  (∃! t : Trade, Replicates m t H) ∧ (∃! p : ℝ, ClaimNoArbitrage m H p) ∧ (∃ sys : FinancialDerivatives.FD01.FinitePriceSystem Bool, sys.statePrice true = riskNeutralUp m / m.growth ∧ sys.statePrice false = (1 - riskNeutralUp m) / m.growth ∧ sys.price H = riskNeutralValue m H ∧ (∀ p : ℝ, ClaimNoArbitrage m H p ↔ p = sys.price H)) := by
  obtain ⟨hq0, hq1⟩ := q_bounds m hNA
  refine ⟨⟨replicatingTrade m H, rep_pay m H, fun b hb => ?_⟩,
    ⟨riskNeutralValue m H, fair m hNA H, fun p hp => claimNA_imp m H p hp⟩,
    ⟨toFD01PriceSystem m hq0 hq1, rfl, rfl, price_eq m hq0 hq1 H, fun p => by
      rw [price_eq]; exact claimNA_iff m hNA H p⟩⟩
  have hs := m.spot_pos
  have hg := m.growth_pos
  have hdu : 0 < m.up - m.down := by linarith [m.down_lt_up]
  have hr := rep_pay m H
  have h1 := hb true; have h2 := hr true; have h3 := hb false; have h4 := hr false
  generalize replicatingTrade m H = a at h2 h4 ⊢
  simp only [terminalPayoff] at h1 h2 h3 h4
  have e : (b.shares - a.shares) * (m.spot * (m.up - m.down)) = 0 := by linarith
  have hsh : b.shares = a.shares := by
    have := (mul_eq_zero.1 e).resolve_right (mul_pos hs hdu).ne'
    linarith
  have hc : b.cash = a.cash := by
    rw [hsh] at h1
    have : (b.cash - a.cash) * m.growth = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hg.ne'
    linarith
  cases a; cases b
  simp_all
