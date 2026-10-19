-- Prove2me | solution 1 for CohnElkies.lower_positiveLogRatio_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/5018ba7d-bf70-4968-a7ba-266205adf56e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_strip_exp_abs_integrable
import Theorems.Thm_CohnElkies_strip_exp_abs_log_abs_integrable

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
    {A : ℝ} (hA : 0 < A) :
    Integrable (fun y : ℝ =>
      max (Real.log (A / |y|)) 0) := by
  let B : ℝ := max 1 A
  have hB : 0 ≤ B := le_trans (by norm_num) (le_max_left 1 A)
  have hbase := strip_exp_abs_integrable
    (by norm_num : 0 < (1 : ℝ))
  have hlog := strip_exp_abs_log_abs_integrable
    (by norm_num : 0 < (1 : ℝ))
  have hnear : Integrable (fun y : ℝ =>
      |Real.log A| * Real.exp ((-1 : ℝ) * |y|) +
        Real.exp ((-1 : ℝ) * |y|) *
          |Real.log (|y|)|) :=
    (hbase.const_mul |Real.log A|).add hlog
  have hmajor : Integrable (fun y : ℝ =>
      Real.exp B *
        (|Real.log A| * Real.exp ((-1 : ℝ) * |y|) +
          Real.exp ((-1 : ℝ) * |y|) *
            |Real.log (|y|)|)) :=
    hnear.const_mul (Real.exp B)
  apply hmajor.mono'
  · have harg : Measurable (fun y : ℝ => A / |y|) := by
      fun_prop
    exact (harg.log.max measurable_const).aestronglyMeasurable
  · filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    by_cases hy : y = 0
    · subst y
      simp
      positivity
    · by_cases hsmall : |y| ≤ B
      · have habslog :
            Real.log (A / |y|) ≤
              |Real.log A| + |Real.log (|y|)| := by
          rw [Real.log_div hA.ne' (abs_ne_zero.mpr hy)]
          linarith [le_abs_self (Real.log A),
            neg_le_abs (Real.log (|y|))]
        have hpoly : 0 ≤
            |Real.log A| + |Real.log (|y|)| := by positivity
        have hmax :
            max (Real.log (A / |y|)) 0 ≤
              |Real.log A| + |Real.log (|y|)| :=
          max_le habslog hpoly
        have hfactor :
            1 ≤ Real.exp B * Real.exp ((-1 : ℝ) * |y|) := by
          rw [← Real.exp_add]
          exact (Real.one_le_exp_iff).2 (by linarith)
        have hproduct :
            |Real.log A| + |Real.log (|y|)| ≤
              (Real.exp B * Real.exp ((-1 : ℝ) * |y|)) *
                (|Real.log A| + |Real.log (|y|)|) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hpoly]
        calc
          max (Real.log (A / |y|)) 0 ≤
              |Real.log A| + |Real.log (|y|)| := hmax
          _ ≤ (Real.exp B * Real.exp ((-1 : ℝ) * |y|)) *
                (|Real.log A| + |Real.log (|y|)|) := hproduct
          _ = Real.exp B *
              (|Real.log A| * Real.exp ((-1 : ℝ) * |y|) +
                Real.exp ((-1 : ℝ) * |y|) *
                  |Real.log (|y|)|) := by ring
      · have hylarge : B < |y| := lt_of_not_ge hsmall
        have hyle : A ≤ |y| :=
          le_trans (le_max_right 1 A) hylarge.le
        have hratio : A / |y| ≤ 1 :=
          (div_le_one (abs_pos.mpr hy)).2 hyle
        have hlognonpos : Real.log (A / |y|) ≤ 0 :=
          Real.log_nonpos
            (div_nonneg hA.le (abs_nonneg y)) hratio
        rw [max_eq_right hlognonpos]
        positivity
end CohnElkies
