-- Prove2me | solution 1 for CohnElkies.stripNormalizedPoissonExtension_continuousAt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/abd24f97-081a-455e-9fdf-57a934c9f291

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (T : ℝ) :
    ContinuousAt (fun σ : ℝ => stripNormalizedPoissonExtension σ T)
      1 := by
  unfold stripNormalizedPoissonExtension
  have hangle : Continuous
      (fun σ : ℝ => Real.pi * (1 - σ) / 2) := by
    fun_prop
  have hden :
      Real.cosh (Real.pi * T / 2) +
        Real.cos (Real.pi * (1 - (1 : ℝ)) / 2) ≠ 0 := by
    simp only [sub_self, mul_zero, zero_div, Real.cos_zero]
    have hcosh := Real.one_le_cosh (Real.pi * T / 2)
    linarith
  exact
    ((continuous_const.mul
      (Real.continuous_sinc.comp hangle)).continuousAt.div
        ((continuous_const.add
          (Real.continuous_cos.comp hangle)).continuousAt) hden)
end CohnElkies
