-- Prove2me | solution 2 for CohnElkies.integral_upperGammaQuadraticKernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:35:40.498019+00:00
-- url     : https://prove2.me/submissions/04374471-251b-4051-a738-3383666dbe7a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ)
    (T : ℝ) :
    (∫ a : ℝ in Ioi 0,
      upperGammaQuadraticKernel ℓ η T a) =
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ) := by
  unfold upperGammaQuadraticKernel upperGammaVariance
  rw [integral_complex_ofReal]
  congr 1
  rw [show (fun a : ℝ => (a * T) ^ 2 / 2 * upperGammaMeasureDensity ℓ η a) =
      fun a : ℝ => (T ^ 2 / 2) * (a ^ 2 * upperGammaMeasureDensity ℓ η a) by
    funext a; ring, integral_const_mul]
  field_simp

