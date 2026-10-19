-- Prove2me | solution 1 for CohnElkies.exp_saddleSourceCenteredPhase_eq_gaussian_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/d80fa341-cdcd-4e56-b7a4-2be08e55ccf2

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
    Complex.exp (saddleSourceCenteredPhase ε ℓ u T) =
      (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
        Complex.exp
          (saddleSourceGaussianPhaseRemainder ε ℓ u T) := by
  unfold saddleSourceGaussianKernel
    saddleSourceGaussianPhaseRemainder
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring
end CohnElkies
