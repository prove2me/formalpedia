-- Prove2me | solution 2 for CohnElkies.saddleSourceContour_piExponential_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:22.018332+00:00
-- url     : https://prove2.me/submissions/e362a3a0-8c08-480e-8386-b9b9d7772d79

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
    (ℓ u T : ℝ) :
    Complex.exp
        (((ℓ : ℂ) - saddleSourceMellinContour ℓ u T) *
          (Real.log Real.pi : ℂ) / 2) =
      (Real.exp (-(ℓ * u) * Real.log Real.pi / 2) : ℂ) *
        Complex.exp
          (Complex.I *
            ((ℓ * T * Real.log Real.pi / 2 : ℝ) : ℂ)) := by
  unfold saddleSourceMellinContour
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

