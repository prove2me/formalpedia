-- Prove2me | solution 1 for CohnElkies.saddleSourceStationaryFrequencyPhase_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/9bfa902b-5710-4952-86fb-e82c29fb7867

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
        (Complex.I *
          ((ℓ * T * Real.log Real.pi / 2 : ℝ) : ℂ)) *
      Complex.exp
        (Complex.I *
          ((ℓ * T *
            saddleSourceStationaryLogRadius ε ℓ u : ℝ) : ℂ)) =
    Complex.exp
        (Complex.I *
          ((ℓ * T / 2 *
            saddleDigamma (ℓ * (1 + u) / 2) : ℝ) : ℂ)) *
      Complex.exp
        (Complex.I *
          ((ℓ * T * saddleSourceShellDerivative ε u : ℝ) : ℂ)) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold saddleSourceStationaryLogRadius
  push_cast
  ring
end CohnElkies
