-- Prove2me | solution 1 for FinancialDerivatives.FD06.heatKernel_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:06:16.644219+00:00
-- url     : https://prove2.me/submissions/f3a6b427-075e-4863-9bb3-675b0fc20866

import Mathlib
import Definitions.Def_fd06_heatKernel

open FinancialDerivatives.FD06

theorem solution (τ x : ℝ) (hτ : 0 < τ) : 0 < heatKernel τ x := by
  unfold heatKernel; positivity
