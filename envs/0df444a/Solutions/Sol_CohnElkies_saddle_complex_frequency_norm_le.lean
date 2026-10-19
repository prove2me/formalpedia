-- Prove2me | solution 1 for CohnElkies.saddle_complex_frequency_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/cfaef852-c3df-4224-8fc6-36ab815299c8

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution (T u : ℝ) :
    ‖(T : ℂ) + Complex.I * (u : ℂ)‖ ≤ |T| + |u| := by
  calc
    ‖(T : ℂ) + Complex.I * (u : ℂ)‖ ≤
        ‖(T : ℂ)‖ + ‖Complex.I * (u : ℂ)‖ :=
      norm_add_le _ _
    _ = |T| + |u| := by
      simp [Complex.norm_real, Real.norm_eq_abs]
end CohnElkies
