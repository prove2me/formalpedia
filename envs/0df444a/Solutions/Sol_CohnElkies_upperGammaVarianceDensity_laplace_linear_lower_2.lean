-- Prove2me | solution 2 for CohnElkies.upperGammaVarianceDensity_laplace_linear_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:26:40.664431+00:00
-- url     : https://prove2.me/submissions/a273e63e-b10f-4487-ba8a-80427c0c92e6

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    a * Real.exp (-η * a) ≤
      a ^ 2 * upperGammaMeasureDensity ℓ η a := by
  unfold upperGammaMeasureDensity
  have hq : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.2 (by have := div_pos (by linarith : 0 < 2*a) hℓ; linarith)
  have h1 : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by linarith
  have h2 : 1 - Real.exp (-(2 * a / ℓ)) ≤ 1 := by linarith [Real.exp_pos (-(2 * a / ℓ))]
  have hE := Real.exp_pos (-η * a)
  rw [show a ^ 2 * (Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ))))) =
      a * Real.exp (-η * a) / (1 - Real.exp (-(2 * a / ℓ))) by field_simp]
  rw [le_div_iff₀ h1]
  exact mul_le_of_le_one_right (by positivity) h2

