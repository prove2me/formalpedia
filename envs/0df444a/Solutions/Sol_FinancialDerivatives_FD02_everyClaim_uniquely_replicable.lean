-- Prove2me | solution 1 for FinancialDerivatives.FD02.everyClaim_uniquely_replicable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:14:02.097348+00:00
-- url     : https://prove2.me/submissions/483dda20-f657-4e0f-a61d-507d78069830

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_Replicates
import Definitions.Def_fd02_replicatingTrade
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (H : Bool → ℝ) :
  ∃! t : Trade, Replicates m t H := by
  have hs := m.spot_pos
  have hg := m.growth_pos
  have hdu : 0 < m.up - m.down := by linarith [m.down_lt_up]
  refine ⟨replicatingTrade m H, ?_, ?_⟩
  · intro ω
    cases ω <;> simp only [terminalPayoff, replicatingTrade] <;> field_simp <;> ring
  · intro b hb
    have hr : Replicates m (replicatingTrade m H) H := by
      intro ω
      cases ω <;> simp only [terminalPayoff, replicatingTrade] <;> field_simp <;> ring
    have h1 := hb true; have h2 := hr true; have h3 := hb false; have h4 := hr false
    simp only [terminalPayoff] at h1 h2 h3 h4
    set a := replicatingTrade m H
    have e : (b.shares - a.shares) * (m.spot * (m.up - m.down)) = 0 := by linarith
    have hsh : b.shares = a.shares := by
      have := (mul_eq_zero.1 e).resolve_right (mul_pos hs hdu).ne'
      linarith
    have hc : b.cash = a.cash := by
      rw [hsh] at h1
      have : (b.cash - a.cash) * m.growth = 0 := by linarith
      have := (mul_eq_zero.1 this).resolve_right hg.ne'
      linarith
    clear_value a
    cases a; cases b
    simp_all
