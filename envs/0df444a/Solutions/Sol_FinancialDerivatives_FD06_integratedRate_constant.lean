-- Prove2me | solution 1 for FinancialDerivatives.FD06.integratedRate_constant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:08:45.336064+00:00
-- url     : https://prove2.me/submissions/c9bfdd41-1f75-4746-93e0-7a9edb14d3d0

import Mathlib
import Definitions.Def_fd06_integratedRate

open FinancialDerivatives.FD06

theorem solution (r t T : ℝ) : integratedRate (fun _ => r) t T = r * (T - t) := by
  unfold integratedRate; simp; ring
