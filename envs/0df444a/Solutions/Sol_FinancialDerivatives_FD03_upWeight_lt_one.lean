-- Prove2me | solution 1 for FinancialDerivatives.FD03.upWeight_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:58:22.250989+00:00
-- url     : https://prove2.me/submissions/db2d39d8-26f5-418f-b53e-50202776ecd4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_fd03_upWeight
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket) :
    upWeight m < 1 := by
  unfold upWeight
  have h1 := m.down_lt_growth
  have h2 := m.growth_lt_up
  rw [div_lt_one (by linarith)]
  linarith
