-- Prove2me | solution 1 for FinancialDerivatives.FD03.oneStep_discount_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:07:35.09883+00:00
-- url     : https://prove2.me/submissions/c765c27d-6a23-4017-bad6-6170acd959ab

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket) :
    0 < (1 / m.growth : ℝ) := by
  exact one_div_pos.mpr (by linarith [m.down_pos, m.down_lt_growth])


