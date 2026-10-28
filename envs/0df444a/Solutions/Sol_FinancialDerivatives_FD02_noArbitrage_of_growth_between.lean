-- Prove2me | solution 1 for FinancialDerivatives.FD02.noArbitrage_of_growth_between
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:58:57.661148+00:00
-- url     : https://prove2.me/submissions/5ab9e1a9-ab4a-401a-b3bf-3ad68017669e

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_NoArbitrage
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (hd : m.down < m.growth) (hu : m.growth < m.up) :
  NoArbitrage m := by
  intro t h h1 h2
  have hs := m.spot_pos
  simp only [initialCost] at h
  have hc : t.cash = -t.shares * m.spot := by linarith
  simp only [terminalPayoff] at h1 h2 ⊢
  rw [hc] at h1 h2 ⊢
  have e1 : t.shares * m.spot * m.up + -t.shares * m.spot * m.growth =
      (t.shares * m.spot) * (m.up - m.growth) := by ring
  have e2 : t.shares * m.spot * m.down + -t.shares * m.spot * m.growth =
      (t.shares * m.spot) * (m.down - m.growth) := by ring
  rw [e1] at h1 ⊢; rw [e2] at h2 ⊢
  have ha : 0 ≤ t.shares * m.spot := by
    by_contra hn; push_neg at hn; nlinarith
  have hb : t.shares * m.spot ≤ 0 := by
    by_contra hn; push_neg at hn; nlinarith
  have : t.shares * m.spot = 0 := le_antisymm hb ha
  simp [this]
