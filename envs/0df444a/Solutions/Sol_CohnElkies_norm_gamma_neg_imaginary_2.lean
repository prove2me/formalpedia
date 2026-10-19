-- Prove2me | solution 2 for CohnElkies.norm_gamma_neg_imaginary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:34.570529+00:00
-- url     : https://prove2.me/submissions/ccebc5e6-dbd7-4e7e-bac9-76eb5931fce0

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


theorem solution (y : ℝ) :
    ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ =
      ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ := by
  have h : -Complex.I * (y : ℂ) / 2 = (starRingEnd ℂ) (Complex.I * (y : ℂ) / 2) := by
    rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal,
      show (starRingEnd ℂ) 2 = 2 from map_ofNat _ 2]
    try ring
  rw [h, Complex.Gamma_conj, Complex.norm_conj]

