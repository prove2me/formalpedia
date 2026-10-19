-- Prove2me | solution 1 for CohnElkies.upperGammaQuadraticKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/2529f0b1-513b-4e41-a831-eb082a5ad038

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_integrable

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
    IntegrableOn (upperGammaQuadraticKernel ℓ η T)
      (Ioi 0) := by
  have hvariance :=
    upperGammaVarianceDensity_integrable hℓ hη
  have hreal : IntegrableOn
      (fun a : ℝ =>
        (T ^ 2 / 2) *
          (a ^ 2 * upperGammaMeasureDensity ℓ η a))
      (Ioi 0) := hvariance.const_mul (T ^ 2 / 2)
  have hcomplex : IntegrableOn
      (fun a : ℝ =>
        (((T ^ 2 / 2) *
          (a ^ 2 * upperGammaMeasureDensity ℓ η a) : ℝ) : ℂ))
      (Ioi 0) := hreal.ofReal
  apply hcomplex.congr_fun _ measurableSet_Ioi
  intro a ha
  unfold upperGammaQuadraticKernel
  apply congrArg Complex.ofReal
  ring
end CohnElkies
