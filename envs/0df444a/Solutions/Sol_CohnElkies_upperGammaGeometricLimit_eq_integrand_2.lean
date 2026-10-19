-- Prove2me | solution 2 for CohnElkies.upperGammaGeometricLimit_eq_integrand
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:51.702164+00:00
-- url     : https://prove2.me/submissions/76f2dd79-4681-47f7-aff8-8ea868045612

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
    upperCosLaplaceKernel η T a *
        (1 - Real.exp (-(2 * a / ℓ)))⁻¹ =
      upperGammaDampingIntegrand ℓ η T a := by
  unfold upperCosLaplaceKernel upperGammaDampingIntegrand upperGammaMeasureDensity
  simp only [div_eq_mul_inv, mul_inv]
  ring

