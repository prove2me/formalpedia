-- Prove2me | solution 1 for FinancialDerivatives.FD03.snell_disallowed_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:59:54.92225+00:00
-- url     : https://prove2.me/submissions/2f3e2535-3169-4840-a7e5-b0808e7ec7b3

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_snellValue
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (reward : ℝ) (u d : ExerciseTree n) :
    snellValue m (n + 1) (.node false reward u d) =
      oneStepValue m (snellValue m n u) (snellValue m n d) := by
  rfl

