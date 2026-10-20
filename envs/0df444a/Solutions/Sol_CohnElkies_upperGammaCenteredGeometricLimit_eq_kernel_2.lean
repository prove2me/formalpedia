-- Prove2me | solution 2 for CohnElkies.upperGammaCenteredGeometricLimit_eq_kernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:35:05.944004+00:00
-- url     : https://prove2.me/submissions/ff72a44f-d586-46b9-994c-58f53194ee10

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    (ℓ η T a : ℝ) :
    upperCenteredLaplaceKernel η T a *
        (((1 - Real.exp (-(2 * a / ℓ)))⁻¹ : ℝ) : ℂ) =
      upperGammaCenteredKernel ℓ η T a := by
  unfold upperCenteredLaplaceKernel upperGammaCenteredKernel upperGammaMeasureDensity
  rw [mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← div_eq_mul_inv, div_div]

