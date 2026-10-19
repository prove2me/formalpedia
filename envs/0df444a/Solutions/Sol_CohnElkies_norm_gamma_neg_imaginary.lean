-- Prove2me | solution 1 for CohnElkies.norm_gamma_neg_imaginary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/196a7dc6-82f9-468b-b7c1-69daeea45b22

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution (y : ℝ) :
    ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ =
      ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ := by
  have harg :
      -Complex.I * (y : ℂ) / 2 =
        starRingEnd ℂ (Complex.I * (y : ℂ) / 2) := by
    simp only [map_div₀, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.conj_ofNat]
  rw [harg, Complex.Gamma_conj, RCLike.norm_conj]
end CohnElkies
