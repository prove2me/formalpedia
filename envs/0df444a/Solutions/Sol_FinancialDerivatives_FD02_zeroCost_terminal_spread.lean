-- Prove2me | solution 1 for FinancialDerivatives.FD02.zeroCost_terminal_spread
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:57:41.456726+00:00
-- url     : https://prove2.me/submissions/3372b24e-bb8f-4533-bd6c-2ce061acb0d7

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (t : Trade) (h : initialCost m t = 0) :
  t.cash = -t.shares * m.spot ∧ terminalPayoff m t true = t.shares * m.spot * (m.up - m.growth) ∧ terminalPayoff m t false = t.shares * m.spot * (m.down - m.growth) := by
  simp only [initialCost] at h
  have hc : t.cash = -t.shares * m.spot := by linarith
  refine ⟨hc, ?_, ?_⟩ <;> simp only [terminalPayoff] <;> rw [hc] <;> ring
