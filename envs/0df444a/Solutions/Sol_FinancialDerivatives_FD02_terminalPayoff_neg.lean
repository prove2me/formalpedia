-- Prove2me | solution 1 for FinancialDerivatives.FD02.terminalPayoff_neg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:57:41.786181+00:00
-- url     : https://prove2.me/submissions/16f32913-43d2-4cd1-adb5-05b7d73a9e52

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (t : Trade) (ω : Bool) :
  terminalPayoff m ({ shares := -t.shares, cash := -t.cash } : Trade) ω = -terminalPayoff m t ω := by
  cases ω <;> simp only [terminalPayoff] <;> ring
