-- Prove2me | solution 1 for FickDiffusion.heatKernel_integral_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:02:52.034322+00:00
-- url     : https://prove2.me/submissions/39b2b83e-e567-447f-9559-9484a74dfa85

import Mathlib
import Definitions.Def_FickDiffusion_defs
open Real Filter Topology MeasureTheory FickDiffusion

theorem solution (D : ℝ) (hD : 0 < D) (t : ℝ) (ht : 0 < t) :
    ∫ x, heatKernel D x t = 1 := by
  unfold heatKernel
  rw [integral_const_mul]
  have hb : 0 < 1 / (4 * D * t) := by positivity
  have h := integral_gaussian (1 / (4 * D * t))
  have e : (fun x : ℝ => Real.exp (-x ^ 2 / (4 * D * t))) =
      fun x => Real.exp (-(1 / (4 * D * t)) * x ^ 2) := by
    funext x; congr 1; ring
  rw [e, h]
  have hpos : 0 < 4 * π * D * t := by positivity
  rw [show π / (1 / (4 * D * t)) = 4 * π * D * t by field_simp]
  rw [one_div_mul_cancel (Real.sqrt_pos.mpr hpos).ne']
