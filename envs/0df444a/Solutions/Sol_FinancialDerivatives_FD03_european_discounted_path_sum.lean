-- Prove2me | solution 1 for FinancialDerivatives.FD03.european_discounted_path_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:11:34.128433+00:00
-- url     : https://prove2.me/submissions/9553d12c-ffd1-4563-805f-43b10a25931c

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_weightedPathSum
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket)
    (n : ℕ) (claim : PayoffTree n) :
    europeanValue m n claim =
      weightedPathSum m n claim / m.growth ^ n := by
  have hud : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
  have hg : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
  induction claim with
  | leaf c => show c = c / m.growth ^ 0; simp
  | branch u d ihu ihd =>
    show oneStepValue m _ _ = (upWeight m * weightedPathSum m _ u + (1 - upWeight m) * weightedPathSum m _ d) / _
    rw [ihu, ihd]
    unfold oneStepValue
    field_simp
    ring


