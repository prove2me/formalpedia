-- Prove2me | solution 1 for FinancialDerivatives.FD06.integratedYield_constant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:10:26.266148+00:00
-- url     : https://prove2.me/submissions/68ce7049-68a8-4730-a9de-21479933da72

import Mathlib
import Definitions.Def_fd06_integratedYield

open FinancialDerivatives.FD06

theorem solution (q t T : ℝ) : integratedYield (fun _ => q) t T = q * (T - t) := by
  unfold integratedYield; simp; ring
