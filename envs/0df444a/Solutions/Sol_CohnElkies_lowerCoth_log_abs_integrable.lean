-- Prove2me | solution 1 for CohnElkies.lowerCoth_log_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/2ea4fa58-2ef2-4c56-b2ee-875aac23f009

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_strip_exp_abs_integrable
import Theorems.Thm_CohnElkies_strip_exp_abs_log_abs_integrable
import Theorems.Thm_CohnElkies_lowerCoth_log_nonneg
import Theorems.Thm_CohnElkies_lowerCoth_log_le_four_exp_neg_two
import Theorems.Thm_CohnElkies_lowerCoth_log_small_abs_bound

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution :
    Integrable (fun y : ℝ =>
      Real.log (lowerCoth (Real.pi * |y| / 2))) := by
  let A : ℝ :=
    Real.pi + |Real.log Real.pi| + 3 * |Real.log (2 : ℝ)|
  have hA : 0 ≤ A := by
    try dsimp [A]
    positivity
  have hbase := strip_exp_abs_integrable
    (by norm_num : 0 < (1 : ℝ))
  have hlog := strip_exp_abs_log_abs_integrable
    (by norm_num : 0 < (1 : ℝ))
  have hnear : Integrable (fun y : ℝ =>
      A * Real.exp ((-1 : ℝ) * |y|) +
        3 * (Real.exp ((-1 : ℝ) * |y|) *
          |Real.log (|y|)|)) :=
    (hbase.const_mul A).add (hlog.const_mul 3)
  have hfar : Integrable (fun y : ℝ =>
      4 * Real.exp ((-Real.pi) * |y|)) :=
    (strip_exp_abs_integrable Real.pi_pos).const_mul 4
  have hmajor : Integrable (fun y : ℝ =>
      Real.exp 1 *
        (A * Real.exp ((-1 : ℝ) * |y|) +
          3 * (Real.exp ((-1 : ℝ) * |y|) *
            |Real.log (|y|)|)) +
        4 * Real.exp ((-Real.pi) * |y|)) :=
    (hnear.const_mul (Real.exp 1)).add hfar
  apply hmajor.mono'
  · have harg : Measurable (fun y : ℝ => Real.pi * |y| / 2) := by
      fun_prop
    have hcoth : Measurable (fun y : ℝ =>
        lowerCoth (Real.pi * |y| / 2)) := by
      unfold lowerCoth
      exact
        (Real.continuous_cosh.measurable.comp harg).div
          (Real.continuous_sinh.measurable.comp harg)
    exact hcoth.log.aestronglyMeasurable
  · filter_upwards [] with y
    by_cases hy : y = 0
    · subst y
      simp [lowerCoth, A]
      positivity
    · have hlognonneg :
          0 ≤ Real.log (lowerCoth (Real.pi * |y| / 2)) :=
        lowerCoth_log_nonneg (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg hlognonneg]
      have hfar_nonneg : 0 ≤
          4 * Real.exp ((-Real.pi) * |y|) := by positivity
      have hnear_nonneg : 0 ≤
          Real.exp 1 *
            (A * Real.exp ((-1 : ℝ) * |y|) +
              3 * (Real.exp ((-1 : ℝ) * |y|) *
                |Real.log (|y|)|)) := by positivity
      by_cases hsmall : |y| ≤ 1
      · have hsmallbound :=
          lowerCoth_log_small_abs_bound hy hsmall
        have hfactor :
            1 ≤ Real.exp 1 * Real.exp ((-1 : ℝ) * |y|) := by
          rw [← Real.exp_add]
          exact (Real.one_le_exp_iff).2 (by linarith)
        have hpolynonneg : 0 ≤ A + 3 * |Real.log (|y|)| := by
          positivity
        have hproduct :
            A + 3 * |Real.log (|y|)| ≤
              (Real.exp 1 * Real.exp ((-1 : ℝ) * |y|)) *
                (A + 3 * |Real.log (|y|)|) := by
          nlinarith [mul_nonneg
            (sub_nonneg.mpr hfactor) hpolynonneg]
        have hrewrite :
            (Real.exp 1 * Real.exp ((-1 : ℝ) * |y|)) *
                (A + 3 * |Real.log (|y|)|) =
              Real.exp 1 *
                (A * Real.exp ((-1 : ℝ) * |y|) +
                  3 * (Real.exp ((-1 : ℝ) * |y|) *
                    |Real.log (|y|)|)) := by
          ring
        try dsimp [A] at hsmallbound ⊢
        try dsimp [A] at hproduct hrewrite
        linarith
      · have hylarge : 1 < |y| := lt_of_not_ge hsmall
        have harg : 1 ≤ Real.pi * |y| / 2 := by
          nlinarith [Real.pi_gt_three,
            mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 2)
              (sub_nonneg.mpr hylarge.le)]
        have hbound := lowerCoth_log_le_four_exp_neg_two harg
        have hexp :
            Real.exp (-2 * (Real.pi * |y| / 2)) =
              Real.exp ((-Real.pi) * |y|) := by
          congr 1
          ring
        rw [hexp] at hbound
        linarith
end CohnElkies
