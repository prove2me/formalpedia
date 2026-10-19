-- Prove2me | solution 1 for CohnElkies.upperGammaCenteredPhase_add_quadratic_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/3e2dfad0-41d5-4da1-94d9-b4f1463cb072

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaCenteredKernel_integrable
import Theorems.Thm_CohnElkies_upperGammaQuadraticKernel_integrable
import Theorems.Thm_CohnElkies_integral_upperGammaQuadraticKernel

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    upperGammaCenteredPhase ℓ η T +
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ) =
      ∫ a : ℝ in Ioi 0,
        upperGammaCubicRemainderKernel ℓ η T a := by
  have hcenter :=
    upperGammaCenteredKernel_integrable hℓ hη T
  have hquad :=
    upperGammaQuadraticKernel_integrable hℓ hη T
  rw [← integral_upperGammaQuadraticKernel hℓ T]
  unfold upperGammaCenteredPhase
  rw [← MeasureTheory.integral_add hcenter hquad]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro a ha
  unfold upperGammaCenteredKernel
    upperGammaQuadraticKernel
    upperGammaCubicRemainderKernel
  push_cast
  ring
end CohnElkies
