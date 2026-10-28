-- Prove2me | solution 1 for FinancialDerivatives.FD02.replicatingTrade_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:13:22.769411+00:00
-- url     : https://prove2.me/submissions/e05ac48d-b423-44e7-957a-8d22a75d5246

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_Replicates
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (H : Bool → ℝ) (a b : Trade) (ha : Replicates m a H) (hb : Replicates m b H) :
  a = b := by
  have hs := m.spot_pos
  have hg := m.growth_pos
  have hdu : 0 < m.up - m.down := by linarith [m.down_lt_up]
  have h1 := ha true; have h2 := hb true; have h3 := ha false; have h4 := hb false
  simp only [terminalPayoff] at h1 h2 h3 h4
  have e : (a.shares - b.shares) * (m.spot * (m.up - m.down)) = 0 := by linarith
  have hsh : a.shares = b.shares := by
    have := (mul_eq_zero.1 e).resolve_right (mul_pos hs hdu).ne'
    linarith
  have hc : a.cash = b.cash := by
    rw [hsh] at h1
    have : (a.cash - b.cash) * m.growth = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hg.ne'
    linarith
  cases a; cases b
  simp_all
