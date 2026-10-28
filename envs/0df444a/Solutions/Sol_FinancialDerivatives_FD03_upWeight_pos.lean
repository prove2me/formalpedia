-- Prove2me | solution 1 for FinancialDerivatives.FD03.upWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:58:18.125833+00:00
-- url     : https://prove2.me/submissions/bd43761a-5c40-4939-b2d8-03b02cf087e8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_fd03_upWeight
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket) :
    0 < upWeight m := by
  unfold upWeight
  have h1 := m.down_lt_growth
  have h2 := m.growth_lt_up
  apply div_pos <;> linarith
