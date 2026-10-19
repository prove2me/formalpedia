-- Prove2me | solution 2 for CohnElkies.lower_positiveLogRatio_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:12:04.769103+00:00
-- url     : https://prove2.me/submissions/bdb40b1f-91d1-4396-8d32-eb13a4f29046

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


theorem solution
    {A : ℝ} (hA : 0 < A) :
    Integrable (fun y : ℝ =>
      max (Real.log (A / |y|)) 0) := by
  have hsupp : Function.support (fun y : ℝ => max (Real.log (A / |y|)) 0) ⊆ Icc (-A) A := by
    intro y hy
    by_contra h
    have hyA : A < |y| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    have hlt : Real.log (A / |y|) < 0 :=
      Real.log_neg (div_pos hA (by linarith)) ((div_lt_one (by linarith)).mpr hyA)
    exact hy (max_eq_right hlt.le)
  refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
  have h1 : IntervalIntegrable (fun y : ℝ => Real.log y) volume (-A) A :=
    intervalIntegral.intervalIntegrable_log'
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at h1
  have hint : IntegrableOn (fun y : ℝ => |Real.log A| + |Real.log y|) (Icc (-A) A) :=
    (continuous_const.integrableOn_Icc).add h1.abs
  have hmeas : Measurable (fun y : ℝ => max (Real.log (A / |y|)) 0) := by
    fun_prop
  refine Integrable.mono' hint hmeas.aestronglyMeasurable (ae_of_all _ (fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  apply max_le _ (by positivity)
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [abs_zero, div_zero, Real.log_zero]; positivity
  · rw [Real.log_div hA.ne' (abs_ne_zero.mpr hy), Real.log_abs]
    linarith [le_abs_self (Real.log A), neg_abs_le (Real.log y)]

