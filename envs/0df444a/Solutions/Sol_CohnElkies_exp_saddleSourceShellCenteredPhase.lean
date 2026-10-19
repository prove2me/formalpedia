-- Prove2me | solution 1 for CohnElkies.exp_saddleSourceShellCenteredPhase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/537523ce-2a8d-41d6-bf32-050fb1b4cba4

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
namespace CohnElkies
theorem _root_.solution
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
  rw [← Complex.exp_add]
  congr 1
  unfold saddleSourceShellCenteredPhase
  push_cast
  ring
end CohnElkies
