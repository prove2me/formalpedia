-- Prove2me | solution 1 for FinancialDerivatives.FD06.integratedVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:09:47.442084+00:00
-- url     : https://prove2.me/submissions/002d7cc3-f8a6-4a28-91db-ae11b9cf4572

import Mathlib
import Definitions.Def_fd06_integratedVariance

open FinancialDerivatives.FD06

theorem solution (σ : ℝ → ℝ) (t T : ℝ) (h : t ≤ T) : 0 ≤ integratedVariance σ t T := by
  unfold integratedVariance; exact intervalIntegral.integral_nonneg h (fun u _ => sq_nonneg _)
