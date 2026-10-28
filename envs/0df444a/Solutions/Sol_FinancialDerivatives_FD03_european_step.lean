-- Prove2me | solution 1 for FinancialDerivatives.FD03.european_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:00:00.612578+00:00
-- url     : https://prove2.me/submissions/37a7af9b-1cea-40a7-a967-c0c757832dc2

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (u d : PayoffTree n) :
    europeanValue m (n + 1) (.branch u d) =
      oneStepValue m (europeanValue m n u) (europeanValue m n d) := by
  rfl

