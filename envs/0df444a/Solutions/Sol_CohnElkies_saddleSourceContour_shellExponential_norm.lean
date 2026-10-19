-- Prove2me | solution 1 for CohnElkies.saddleSourceContour_shellExponential_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/64c5a8b5-ab7d-482f-ab6b-c27b3c42cf44

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceMellinContour_shellArgument
import Theorems.Thm_CohnElkies_norm_saddleShellExponential_eq_exp_neg_damping

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (T : ℝ) :
    ‖Complex.exp
      ((ℓ : ℂ) * mellinShellPhase ε
        (Complex.I *
          (saddleSourceMellinContour ℓ u T - (ℓ : ℂ)) /
            (ℓ : ℂ)))‖ =
      Real.exp (ℓ * realHyperbolicShellPhase ε u) *
        Real.exp
          (-(positiveShellDamping ε ℓ (u - 1) T -
            upperShortShellDamping ε ℓ (u - 1) T)) := by
  rw [saddleSourceMellinContour_shellArgument hℓ]
  exact norm_saddleShellExponential_eq_exp_neg_damping
    hε horder ℓ T u
end CohnElkies
