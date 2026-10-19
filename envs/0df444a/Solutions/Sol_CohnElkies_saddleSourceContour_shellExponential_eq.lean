-- Prove2me | solution 1 for CohnElkies.saddleSourceContour_shellExponential_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/4b2175fd-0e2f-491b-83a0-6d25da4919dc

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
end CohnElkies
