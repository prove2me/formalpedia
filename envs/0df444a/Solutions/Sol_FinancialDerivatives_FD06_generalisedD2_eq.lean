-- Prove2me | solution 1 for FinancialDerivatives.FD06.generalisedD2_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:04:47.046795+00:00
-- url     : https://prove2.me/submissions/0aca8229-98a9-4fe6-a8aa-d5cdfe95bf32

import Mathlib
import Definitions.Def_fd06_generalisedD1
import Definitions.Def_fd06_generalisedD2

open FinancialDerivatives.FD06

theorem solution (S K R Q V : ℝ) : generalisedD2 S K R Q V = generalisedD1 S K R Q V - Real.sqrt V := by
  exact rfl
