-- Prove2me | solution 1 for CohnElkies.saddleNegativeContour_piExponential_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/1799992d-308a-4de6-92e7-ba389b4b6095

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    (ℓ : ℝ) (N : ℕ) (s : ℝ) :
    ‖Complex.exp
      ((((ℓ : ℂ) -
        ((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I)) *
          (Real.log Real.pi : ℂ) / 2))‖ =
      Real.exp
        ((ℓ - saddleTaylorContour N) *
          Real.log Real.pi / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]
end CohnElkies
