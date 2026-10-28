-- Prove2me | solution 1 for FinancialDerivatives.FD03.european_constant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:05:47.402286+00:00
-- url     : https://prove2.me/submissions/c8398d36-0b92-4368-8384-b22873098793

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_constantPayoffTree
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket) (n : ℕ) (c : ℝ) :
    europeanValue m n (constantPayoffTree n c) =
      c / m.growth ^ n := by
  have hud : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
  have hg : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
  induction n with
  | zero => show c = c / m.growth ^ 0; simp
  | succ n ih =>
    show oneStepValue m (europeanValue m n (constantPayoffTree n c)) (europeanValue m n (constantPayoffTree n c)) = _
    rw [ih]
    unfold oneStepValue
    field_simp
    ring


