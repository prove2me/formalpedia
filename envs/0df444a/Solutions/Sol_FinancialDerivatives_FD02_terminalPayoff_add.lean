-- Prove2me | solution 1 for FinancialDerivatives.FD02.terminalPayoff_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:53:53.631166+00:00
-- url     : https://prove2.me/submissions/a63254b6-a8a5-412c-ae83-65506e920e81

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (a b : Trade) (ω : Bool) :
  terminalPayoff m ({ shares := a.shares + b.shares, cash := a.cash + b.cash } : Trade) ω = terminalPayoff m a ω + terminalPayoff m b ω := by
  cases ω <;> simp only [terminalPayoff] <;> ring
