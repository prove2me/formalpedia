-- Prove2me | solution 1 for FinancialDerivatives.FD02.initialCost_neg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:57:41.871993+00:00
-- url     : https://prove2.me/submissions/25cbed69-0073-440d-a576-8a3b6384c29e

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (t : Trade) :
  initialCost m ({ shares := -t.shares, cash := -t.cash } : Trade) = -initialCost m t := by
  simp only [initialCost]; ring
