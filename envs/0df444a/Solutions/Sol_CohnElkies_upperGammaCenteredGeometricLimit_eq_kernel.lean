-- Prove2me | solution 1 for CohnElkies.upperGammaCenteredGeometricLimit_eq_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/1249208b-57f3-4671-8b25-1b8cf36dffa3

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
namespace CohnElkies
theorem _root_.solution
    (ℓ η T a : ℝ) :
    upperCenteredLaplaceKernel η T a *
        (((1 - Real.exp (-(2 * a / ℓ)))⁻¹ : ℝ) : ℂ) =
      upperGammaCenteredKernel ℓ η T a := by
  simp [upperCenteredLaplaceKernel, upperGammaCenteredKernel,
    upperGammaMeasureDensity, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc]
end CohnElkies
