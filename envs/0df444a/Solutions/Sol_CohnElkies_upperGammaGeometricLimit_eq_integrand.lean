-- Prove2me | solution 1 for CohnElkies.upperGammaGeometricLimit_eq_integrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/e0a3738a-f167-4b3b-901a-2252ad88cb36

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
    upperCosLaplaceKernel η T a *
        (1 - Real.exp (-(2 * a / ℓ)))⁻¹ =
      upperGammaDampingIntegrand ℓ η T a := by
  simp [upperCosLaplaceKernel, upperGammaDampingIntegrand,
    upperGammaMeasureDensity, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc]
end CohnElkies
