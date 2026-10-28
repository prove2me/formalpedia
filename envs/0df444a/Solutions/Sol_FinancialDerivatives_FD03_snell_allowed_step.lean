-- Prove2me | solution 1 for FinancialDerivatives.FD03.snell_allowed_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:59:52.138345+00:00
-- url     : https://prove2.me/submissions/57e19488-c3c3-45bd-af15-6bb95ca0a531

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_snellValue
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (reward : ℝ) (u d : ExerciseTree n) :
    snellValue m (n + 1) (.node true reward u d) =
      max reward (oneStepValue m (snellValue m n u) (snellValue m n d)) := by
  rfl

