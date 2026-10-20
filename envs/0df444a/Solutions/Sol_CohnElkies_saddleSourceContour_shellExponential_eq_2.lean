-- Prove2me | solution 2 for CohnElkies.saddleSourceContour_shellExponential_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:34:07.115235+00:00
-- url     : https://prove2.me/submissions/e37a9c2d-c50a-463a-aabd-22b2cf7acbb8

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
    (ε ℓ u T : ℝ) :
    Complex.exp
        ((ℓ : ℂ) *
          mellinShellPhase ε
            ((T : ℂ) + Complex.I * (u : ℂ))) =
      (Real.exp (ℓ * realHyperbolicShellPhase ε u) : ℂ) *
        Complex.exp
          ((ℓ : ℂ) *
            (mellinShellPhase ε
                ((T : ℂ) + Complex.I * (u : ℂ)) -
              (realHyperbolicShellPhase ε u : ℂ))) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

