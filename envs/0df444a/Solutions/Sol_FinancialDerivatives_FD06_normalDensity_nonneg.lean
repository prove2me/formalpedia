-- Prove2me | solution 1 for FinancialDerivatives.FD06.normalDensity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:05:02.646083+00:00
-- url     : https://prove2.me/submissions/18e02a2f-c11b-4fc5-b073-a8d2ca7a51ae

import Mathlib
import Definitions.Def_fd06_standardNormalDensity

open FinancialDerivatives.FD06

theorem solution (x : ℝ) : 0 ≤ standardNormalDensity x := by
  unfold standardNormalDensity; positivity
