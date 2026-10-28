-- Prove2me | solution 1 for FinancialDerivatives.FD06.integratedVariance_constant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:09:31.476831+00:00
-- url     : https://prove2.me/submissions/7c823550-4130-45e6-8729-6e2137f81cd3

import Mathlib
import Definitions.Def_fd06_integratedVariance

open FinancialDerivatives.FD06

theorem solution (σ t T : ℝ) : integratedVariance (fun _ => σ) t T = σ ^ 2 * (T - t) := by
  unfold integratedVariance; simp; ring
