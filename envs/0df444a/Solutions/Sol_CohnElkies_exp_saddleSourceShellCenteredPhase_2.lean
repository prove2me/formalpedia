-- Prove2me | solution 2 for CohnElkies.exp_saddleSourceShellCenteredPhase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:25:28.911607+00:00
-- url     : https://prove2.me/submissions/cfeb8c97-4eca-437f-9a8d-2e884835bfb3

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
    Complex.exp (saddleSourceShellCenteredPhase ε ℓ u T) =
      Complex.exp
        ((ℓ : ℂ) *
          (mellinShellPhase ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            (realHyperbolicShellPhase ε u : ℂ))) *
        Complex.exp
          (Complex.I *
            ((ℓ * T * saddleSourceShellDerivative ε u : ℝ) : ℂ)) := by
  unfold saddleSourceShellCenteredPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

