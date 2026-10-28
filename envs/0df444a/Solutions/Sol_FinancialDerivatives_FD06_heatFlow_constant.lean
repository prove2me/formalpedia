-- Prove2me | solution 1 for FinancialDerivatives.FD06.heatFlow_constant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:05:50.863817+00:00
-- url     : https://prove2.me/submissions/edb78bf1-4c86-4c87-8a2d-7d6c8cb836c1

import Mathlib
import Definitions.Def_fd06_gaussianHeatFlow

open FinancialDerivatives.FD06

theorem solution (c τ x : ℝ) : gaussianHeatFlow (fun _ => c) τ x = c := by
  unfold gaussianHeatFlow; simp
