-- Prove2me | solution 1 for CohnElkies.lower_exp_log_sqrtFactor_integrableOn_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/521f4694-f528-4133-bc48-950a919b3b15

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lower_abs_log_sqrtFactor_le
import Theorems.Thm_CohnElkies_lower_exp_abs_log_div_two_integrableOn_Ioi

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
    {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    IntegrableOn
      (fun y : ℝ => Real.exp ((-a) * y) *
        Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2)))
      (Ioi (0 : ℝ)) := by
  have hexponential :
      IntegrableOn (fun y : ℝ => Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
  have hlinear :
      IntegrableOn
        (fun y : ℝ => y * Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) := by
    simpa [Real.rpow_one] using!
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (1 : ℝ)) (b := a)
        (by norm_num) (by norm_num) ha)
  have hmajorant :
      IntegrableOn
        (fun y : ℝ =>
          c * Real.exp ((-a) * y) +
            (1 / 2 : ℝ) * (y * Real.exp ((-a) * y)) +
            Real.exp ((-a) * y) * |Real.log (y / 2)|)
        (Ioi (0 : ℝ)) :=
    ((hexponential.const_mul c).add (hlinear.const_mul (1 / 2))).add
      (lower_exp_abs_log_div_two_integrableOn_Ioi ha)
  have hcontinuous :
      ContinuousOn
        (fun y : ℝ => Real.exp ((-a) * y) *
          Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2)))
        (Ioi (0 : ℝ)) := by
    apply ContinuousOn.mul
    · fun_prop
    · apply ContinuousOn.log
      · fun_prop
      · intro y hy
        apply (Real.sqrt_pos.2 ?_).ne'
        have ht : 0 < y / 2 := by
          exact half_pos (mem_Ioi.mp hy)
        nlinarith [sq_nonneg c, sq_pos_of_pos ht]
  apply hmajorant.mono'
    (hcontinuous.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hlog := lower_abs_log_sqrtFactor_le hc (mem_Ioi.mp hy)
  change ‖Real.exp ((-a) * y) *
      Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2))‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp ((-a) * y) *
        |Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2))| ≤
      Real.exp ((-a) * y) *
        (c + y / 2 + |Real.log (y / 2)|) :=
      mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
    _ = c * Real.exp ((-a) * y) +
          (1 / 2 : ℝ) * (y * Real.exp ((-a) * y)) +
          Real.exp ((-a) * y) * |Real.log (y / 2)| := by
      ring
end CohnElkies
