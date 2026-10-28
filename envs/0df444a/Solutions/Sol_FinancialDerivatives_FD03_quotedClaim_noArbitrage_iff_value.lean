-- Prove2me | solution 1 for FinancialDerivatives.FD03.quotedClaim_noArbitrage_iff_value
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:12:49.543589+00:00
-- url     : https://prove2.me/submissions/32a9fd08-881d-4a0e-bf42-c3568856681b

import Mathlib.Tactic
import Definitions.Def_fd03_localHedge
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_quotedClaimArbitrage
import Definitions.Def_fd03_europeanValue

namespace S82FD

open FinancialDerivatives.FD03

theorem hud (m : BinomialMarket) : m.up - m.down ≠ 0 := by
  linarith [m.down_lt_growth, m.growth_lt_up]
theorem hgpos (m : BinomialMarket) : 0 < m.growth := by linarith [m.down_pos, m.down_lt_growth]
theorem hupos (m : BinomialMarket) : 0 < m.up := by
  linarith [m.down_pos, m.down_lt_growth, m.growth_lt_up]
theorem w0 (m : BinomialMarket) : 0 < upWeight m := by
  unfold upWeight
  exact div_pos (by linarith [m.down_lt_growth]) (by linarith [m.down_lt_growth, m.growth_lt_up])
theorem w1 (m : BinomialMarket) : upWeight m < 1 := by
  unfold upWeight
  rw [div_lt_one (by linarith [m.down_lt_growth, m.growth_lt_up])]
  linarith [m.growth_lt_up]

theorem sf_wealth (m : BinomialMarket) (spot sh b wu wd : ℝ)
    (h1 : sh * (spot * m.up) + b * m.growth = wu) (h2 : sh * (spot * m.down) + b * m.growth = wd) :
    sh * spot + b = oneStepValue m wu wd := by
  have := hud m
  have := (hgpos m).ne'
  rw [← h1, ← h2]
  unfold oneStepValue upWeight
  field_simp
  ring

theorem lh_up (m : BinomialMarket) (spot vu vd : ℝ) (hspot : 0 < spot) :
    (localHedge m spot vu vd).1 * (spot * m.up) + (localHedge m spot vu vd).2 * m.growth = vu := by
  have := hud m
  have := (hgpos m).ne'
  have := hspot.ne'
  unfold localHedge; dsimp only; field_simp; ring

theorem lh_dn (m : BinomialMarket) (spot vu vd : ℝ) (hspot : 0 < spot) :
    (localHedge m spot vu vd).1 * (spot * m.down) + (localHedge m spot vu vd).2 * m.growth = vd := by
  have := hud m
  have := (hgpos m).ne'
  have := hspot.ne'
  unfold localHedge; dsimp only; field_simp; ring

theorem lh_cost (m : BinomialMarket) (spot vu vd : ℝ) (hspot : 0 < spot) :
    (localHedge m spot vu vd).1 * spot + (localHedge m spot vu vd).2 = oneStepValue m vu vd := by
  have := hud m
  have := (hgpos m).ne'
  have := hspot.ne'
  unfold localHedge oneStepValue upWeight; dsimp only; field_simp; ring

theorem osv_lin (m : BinomialMarket) (a b c d u : ℝ) :
    oneStepValue m a b + u * oneStepValue m c d = oneStepValue m (a + u * c) (b + u * d) := by
  unfold oneStepValue; ring

theorem osv_nonneg (m : BinomialMarket) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ oneStepValue m x y := by
  unfold oneStepValue
  have := w0 m; have := w1 m; have := hgpos m
  apply div_nonneg _ this.le
  nlinarith

theorem osv_pos (m : BinomialMarket) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : 0 < x ∨ 0 < y) :
    0 < oneStepValue m x y := by
  unfold oneStepValue
  have := w0 m; have := w1 m; have := hgpos m
  apply div_pos _ this
  rcases h with h | h <;> nlinarith

/-- arbitrage construction: shifted replicator of `a • claim` with extra capital `k`. -/
theorem shifted (m : BinomialMarket) (n : ℕ) (claim : PayoffTree n) :
    ∀ (spot a k : ℝ), 0 < spot → 0 < k → ∃ hedge : HedgeTree n,
      SelfFinancing m n spot hedge ∧ hedgeWealth m n spot hedge = a * europeanValue m n claim + k ∧
      terminalCombinedNonnegative n hedge claim (-a) ∧
      terminalCombinedPositiveSomewhere n hedge claim (-a) := by
  induction claim with
  | leaf c =>
    intro spot a k _ hk
    refine ⟨.terminal (a * c + k), trivial, rfl, ?_, ?_⟩
    · show 0 ≤ a * c + k + -a * c; linarith
    · show 0 < a * c + k + -a * c; linarith
  | branch cu cd ihu ihd =>
    intro spot a k hspot hk
    have hkg : 0 < k * m.growth := mul_pos hk (hgpos m)
    obtain ⟨hu, hu1, hu2, hu3, hu4⟩ := ihu (spot * m.up) a (k * m.growth) (mul_pos hspot (hupos m)) hkg
    obtain ⟨hd, hd1, hd2, hd3, hd4⟩ := ihd (spot * m.down) a (k * m.growth) (mul_pos hspot m.down_pos) hkg
    set Wu := a * europeanValue m _ cu + k * m.growth
    set Wd := a * europeanValue m _ cd + k * m.growth
    refine ⟨.node (localHedge m spot Wu Wd).1 (localHedge m spot Wu Wd).2 hu hd,
      ⟨?_, ?_, hu1, hd1⟩, ?_, ⟨hu3, hd3⟩, Or.inl hu4⟩
    · rw [hu2]; exact lh_up m spot Wu Wd hspot
    · rw [hd2]; exact lh_dn m spot Wu Wd hspot
    · show _ * spot + _ = a * oneStepValue m _ _ + k
      rw [lh_cost m spot Wu Wd hspot]
      have := (hgpos m).ne'
      simp only [Wu, Wd]
      unfold oneStepValue
      field_simp
      ring

/-- valuation of a self-financing combined position is nonneg / positive. -/
theorem value_bound (m : BinomialMarket) (n : ℕ) (hedge : HedgeTree n) :
    ∀ (spot : ℝ) (claim : PayoffTree n) (units : ℝ), SelfFinancing m n spot hedge →
      terminalCombinedNonnegative n hedge claim units →
      0 ≤ hedgeWealth m n spot hedge + units * europeanValue m n claim ∧
      (terminalCombinedPositiveSomewhere n hedge claim units →
        0 < hedgeWealth m n spot hedge + units * europeanValue m n claim) := by
  induction hedge with
  | terminal cash =>
    intro spot claim units _ hn
    cases claim with
    | leaf p => exact ⟨hn, fun h => h⟩
  | node sh b hu hd ihu ihd =>
    intro spot claim units hsf hn
    cases claim with
    | branch cu cd =>
      obtain ⟨h1, h2, h3, h4⟩ := hsf
      obtain ⟨n1, n2⟩ := hn
      obtain ⟨a1, a2⟩ := ihu _ cu units h3 n1
      obtain ⟨b1, b2⟩ := ihd _ cd units h4 n2
      have e : hedgeWealth m _ spot (.node sh b hu hd) + units * europeanValue m _ (.branch cu cd) =
          oneStepValue m (hedgeWealth m _ (spot * m.up) hu + units * europeanValue m _ cu)
            (hedgeWealth m _ (spot * m.down) hd + units * europeanValue m _ cd) := by
        show sh * spot + b + units * oneStepValue m _ _ = _
        rw [sf_wealth m spot sh b _ _ h1 h2, osv_lin]
      rw [e]
      refine ⟨osv_nonneg m _ _ a1 b1, fun hp => osv_pos m _ _ a1 b1 ?_⟩
      rcases hp with hp | hp
      · exact Or.inl (a2 hp)
      · exact Or.inr (b2 hp)

theorem noarb (m : BinomialMarket) (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (claim : PayoffTree n) (quote : ℝ) :
    ¬ quotedClaimArbitrage m n spot claim quote ↔ quote = europeanValue m n claim := by
  constructor
  · intro h
    by_contra hne
    apply h
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨hedge, h1, h2, h3, h4⟩ := shifted m n claim spot (-1) (europeanValue m n claim - quote)
        hspot (by linarith)
      refine ⟨hedge, 1, h1, ?_, by simpa using h3, by simpa using h4⟩
      rw [h2]; ring
    · obtain ⟨hedge, h1, h2, h3, h4⟩ := shifted m n claim spot 1 (quote - europeanValue m n claim)
        hspot (by linarith)
      refine ⟨hedge, -1, h1, ?_, h3, h4⟩
      rw [h2]; ring
  · rintro rfl ⟨hedge, units, h1, h2, h3, h4⟩
    have := (value_bound m n hedge spot claim units h1 h3).2 h4
    linarith

end S82FD

open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (claim : PayoffTree n) (quote : ℝ) :
    ¬ quotedClaimArbitrage m n spot claim quote ↔
      quote = europeanValue m n claim := by
  exact S82FD.noarb m n spot hspot claim quote


