-- Prove2me | solution 1 for CohnElkies.upperComplex_norm_ratio_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/2e3a499c-05b9-4566-ba51-8905f00b49dc

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
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (T : ℝ) :
    ‖((s * c : ℝ) : ℂ) +
        Complex.I * ((s * T : ℝ) : ℂ)‖ / (s * c) =
      ‖(c : ℂ) + Complex.I * (T : ℂ)‖ / c := by
  have he :
      ((s * c : ℝ) : ℂ) +
          Complex.I * ((s * T : ℝ) : ℂ) =
        (s : ℂ) * ((c : ℂ) + Complex.I * (T : ℂ)) := by
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_of_nonneg hs.le]
  field_simp [hs.ne', hc.ne']
end CohnElkies
