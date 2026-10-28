-- Prove2me | solution 1 for FinancialDerivatives.FD06.heatKernel_mass_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:06:48.636224+00:00
-- url     : https://prove2.me/submissions/fc5ef715-a2dd-4574-a0e4-dec4c0e9d823

import Mathlib
import Definitions.Def_fd06_heatKernel

open FinancialDerivatives.FD06

theorem solution (τ : ℝ) (hτ : 0 < τ) : (∫ x : ℝ, heatKernel τ x) = 1 := by
  have e : ∀ x, heatKernel τ x = Real.exp (-(1/(4*τ)) * x^2) / Real.sqrt (4*Real.pi*τ) := by
    intro x; unfold heatKernel; congr 2; ring
  simp_rw [e]
  rw [MeasureTheory.integral_div, integral_gaussian]
  have : Real.pi / (1 / (4 * τ)) = 4 * Real.pi * τ := by field_simp
  rw [this, div_self]; positivity
