-- Prove2me | solution 2 for CohnElkies.upperComplex_norm_ratio_scale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:09:48.101597+00:00
-- url     : https://prove2.me/submissions/de80408c-2c94-49e9-b9b6-f5efed197ad0

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


theorem solution
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (T : ℝ) :
    ‖((s * c : ℝ) : ℂ) +
        Complex.I * ((s * T : ℝ) : ℂ)‖ / (s * c) =
      ‖(c : ℂ) + Complex.I * (T : ℂ)‖ / c := by
  rw [show (((s * c : ℝ)) : ℂ) + Complex.I * ((s * T : ℝ) : ℂ) = (s : ℂ) * ((c : ℂ) + Complex.I * (T : ℂ)) by push_cast; ring,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  field_simp

