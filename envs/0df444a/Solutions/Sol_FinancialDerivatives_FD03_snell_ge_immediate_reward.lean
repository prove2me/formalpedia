-- Prove2me | solution 1 for FinancialDerivatives.FD03.snell_ge_immediate_reward
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:59:49.125033+00:00
-- url     : https://prove2.me/submissions/c5aabdc8-d186-4036-a424-facf93ecc5d1

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_snellValue
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (reward : ℝ) (u d : ExerciseTree n) :
    reward ≤ snellValue m (n + 1) (.node true reward u d) := by
  show reward ≤ max reward _
  exact le_max_left _ _

