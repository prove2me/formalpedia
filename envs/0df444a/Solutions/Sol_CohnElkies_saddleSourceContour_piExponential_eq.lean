-- Prove2me | solution 1 for CohnElkies.saddleSourceContour_piExponential_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/3de18d42-309b-401b-85d6-527168e08f92

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
    (ℓ u T : ℝ) :
    Complex.exp
        (((ℓ : ℂ) - saddleSourceMellinContour ℓ u T) *
          (Real.log Real.pi : ℂ) / 2) =
      (Real.exp (-(ℓ * u) * Real.log Real.pi / 2) : ℂ) *
        Complex.exp
          (Complex.I *
            ((ℓ * T * Real.log Real.pi / 2 : ℝ) : ℂ)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  unfold saddleSourceMellinContour
  push_cast
  ring
end CohnElkies
