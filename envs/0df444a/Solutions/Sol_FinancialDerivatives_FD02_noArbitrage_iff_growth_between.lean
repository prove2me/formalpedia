-- Prove2me | solution 1 for FinancialDerivatives.FD02.noArbitrage_iff_growth_between
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:02:16.835695+00:00
-- url     : https://prove2.me/submissions/f63ee54c-5383-48c6-aac5-3112678312fe

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_NoArbitrage
open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) :
  NoArbitrage m ↔ m.down < m.growth ∧ m.growth < m.up := by
  have hs := m.spot_pos
  have hdu := m.down_lt_up
  constructor
  · intro hna
    constructor
    · by_contra h
      push_neg at h
      have := hna ⟨1, -m.spot⟩ (by simp [initialCost]) (by simp [terminalPayoff]; nlinarith)
        (by simp [terminalPayoff]; nlinarith)
      simp [terminalPayoff] at this
      nlinarith [this.1]
    · by_contra h
      push_neg at h
      have := hna ⟨-1, m.spot⟩ (by simp [initialCost]) (by simp [terminalPayoff]; nlinarith)
        (by simp [terminalPayoff]; nlinarith)
      simp [terminalPayoff] at this
      nlinarith [this.2]
  · rintro ⟨hd, hu⟩ t h0 h1 h2
    simp only [initialCost] at h0
    simp only [terminalPayoff] at h1 h2 ⊢
    have hc : t.cash = -t.shares * m.spot := by linarith
    rw [hc] at h1 h2 ⊢
    have e1 : t.shares * m.spot * m.up + -t.shares * m.spot * m.growth
        = t.shares * m.spot * (m.up - m.growth) := by ring
    have e2 : t.shares * m.spot * m.down + -t.shares * m.spot * m.growth
        = t.shares * m.spot * (m.down - m.growth) := by ring
    rw [e1] at h1 ⊢; rw [e2] at h2 ⊢
    have hsh : t.shares = 0 := by
      rcases lt_trichotomy t.shares 0 with h | h | h
      · have : t.shares * m.spot * (m.up - m.growth) < 0 := by
          apply mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h hs); linarith
        linarith
      · exact h
      · have : t.shares * m.spot * (m.down - m.growth) < 0 := by
          apply mul_neg_of_pos_of_neg (mul_pos h hs); linarith
        linarith
    simp [hsh]
