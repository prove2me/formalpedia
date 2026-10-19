-- Prove2me | solution 1 for CohnElkies.lower_exp_abs_log_div_two_integrableOn_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/827ac5f7-d6da-4f30-9db5-5c5be747d56e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_strip_exp_abs_log_integrableOn_Ioi

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun y : ℝ =>
        Real.exp ((-a) * y) * |Real.log (y / 2)|)
      (Ioi (0 : ℝ)) := by
  have hexponential :
      IntegrableOn (fun y : ℝ => Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
  have hmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Real.exp ((-a) * y) * |Real.log y| +
            |Real.log (2 : ℝ)| * Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) :=
    (strip_exp_abs_log_integrableOn_Ioi ha).add
      (hexponential.const_mul |Real.log (2 : ℝ)|)
  have hcontinuous :
      ContinuousOn
        (fun y : ℝ =>
          Real.exp ((-a) * y) * |Real.log (y / 2)|)
        (Ioi (0 : ℝ)) := by
    apply ContinuousOn.mul
    · fun_prop
    · apply ContinuousOn.abs
      apply ContinuousOn.log
      · fun_prop
      · intro y hy
        exact div_ne_zero (mem_Ioi.mp hy).ne' (by norm_num)
  apply hmajorant.mono'
    (hcontinuous.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos := mem_Ioi.mp hy
  have hlog :
      |Real.log (y / 2)| ≤ |Real.log y| + |Real.log (2 : ℝ)| := by
    rw [Real.log_div hypos.ne' (by norm_num)]
    exact abs_sub _ _
  change ‖Real.exp ((-a) * y) * |Real.log (y / 2)|‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_abs]
  calc
    Real.exp ((-a) * y) * |Real.log (y / 2)| ≤
        Real.exp ((-a) * y) *
          (|Real.log y| + |Real.log (2 : ℝ)|) :=
      mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
    _ = Real.exp ((-a) * y) * |Real.log y| +
        |Real.log (2 : ℝ)| * Real.exp ((-a) * y) := by
      ring
end CohnElkies
