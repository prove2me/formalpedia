-- Prove2me | solution 1 for FinancialDerivatives.FD02.initialCost_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:53:53.378658+00:00
-- url     : https://prove2.me/submissions/6ac44e38-393c-4c35-a68b-f3e5e9507d36

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (a b : Trade) :
  initialCost m ({ shares := a.shares + b.shares, cash := a.cash + b.cash } : Trade) = initialCost m a + initialCost m b := by
  simp only [initialCost]; ring
