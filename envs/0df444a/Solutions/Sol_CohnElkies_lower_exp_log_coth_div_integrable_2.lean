-- Prove2me | solution 2 for CohnElkies.lower_exp_log_coth_div_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:02:57.203171+00:00
-- url     : https://prove2.me/submissions/f4c550d2-8ddf-4c0b-ab10-491e938de7ad

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
theorem h47b_rpow_exp {s : ℝ} (hs : -1 < s) {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun T : ℝ => |T| ^ s * Real.exp (-a * |T|)) := by
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s) (p := 1) (b := a) hs one_pos ha
  have hIoi : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ s * Real.exp (-a * |T|)) (Set.Ioi 0) := by
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := hx
    simp [abs_of_pos hx0]
  have hIio : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ s * Real.exp (-a * |T|)) (Set.Iio 0) := by
    have := (show MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ s * Real.exp (-a * |T|)) (Set.Ioi (-0)) by
      simpa using hIoi).comp_neg_Iio
    simpa [abs_neg] using this
  have hall : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ s * Real.exp (-a * |T|)) (Set.Iic 0 ∪ Set.Ioi 0) :=
    ((integrableOn_Iic_iff_integrableOn_Iio (b := (0:ℝ))).mpr hIio).union hIoi
  rw [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] at hall
  exact hall

theorem h47b_le {x : ℝ} (hx : 0 < x) :
    |Real.log (lowerCoth (Real.pi * x) / x)| ≤
      2 * (Real.pi * x) +
        |Real.log Real.pi| + 2 * |Real.log x| := by
  have hpi := Real.pi_pos
  have hy : 0 < Real.pi * x := mul_pos hpi hx
  unfold lowerCoth
  have hs : 0 < Real.sinh (Real.pi * x) := Real.sinh_pos_iff.2 hy
  have hcs : Real.sinh (Real.pi * x) ≤ Real.cosh (Real.pi * x) := (Real.sinh_lt_cosh _).le
  have hc1 : 1 ≤ Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x) := (one_le_div hs).2 hcs
  have hcu : Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x) ≤ (Real.pi * x + 1) / (Real.pi * x) := by
    rw [div_le_div_iff₀ hs hy, Real.cosh_eq, Real.sinh_eq]
    have hE := Real.exp_pos (Real.pi * x)
    have hF := Real.exp_pos (-(Real.pi * x))
    have hEF : Real.exp (Real.pi * x) * Real.exp (-(Real.pi * x)) = 1 := by rw [← Real.exp_add]; simp
    have h2 : 2 * (Real.pi * x) + 1 ≤ Real.exp (Real.pi * x) * Real.exp (Real.pi * x) := by
      rw [← Real.exp_add]; linarith [Real.add_one_le_exp (Real.pi * x + Real.pi * x)]
    have h3 : Real.exp (Real.pi * x) * Real.exp (Real.pi * x) * Real.exp (-(Real.pi * x)) = Real.exp (Real.pi * x) := by
      rw [mul_assoc, hEF, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left h2 hF.le, mul_pos hF hy]
  have hlogc : Real.log (Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x)) ≤ Real.pi * x - Real.log Real.pi - Real.log x := by
    have h1 := Real.log_le_log (by linarith) hcu
    rw [Real.log_div (by linarith) hy.ne', Real.log_mul hpi.ne' hx.ne'] at h1
    have h2 : Real.log (Real.pi * x + 1) ≤ Real.pi * x := by
      have := Real.log_le_sub_one_of_pos (show 0 < Real.pi * x + 1 by linarith); linarith
    linarith
  have hlogc0 : 0 ≤ Real.log (Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x)) := Real.log_nonneg hc1
  rw [Real.log_div (by linarith) hx.ne', abs_le]
  constructor <;> linarith [le_abs_self (Real.log Real.pi), neg_abs_le (Real.log Real.pi), le_abs_self (Real.log x), neg_abs_le (Real.log x)]

theorem h47b_abslog {t : ℝ} (ht : 0 < t) : |Real.log t| ≤ t + 2 * t ^ (-(1/2 : ℝ)) := by
  have hr : 0 < t ^ (-(1/2 : ℝ)) := Real.rpow_pos_of_pos ht _
  have h1 := Real.log_le_sub_one_of_pos ht
  have h2 := Real.log_le_sub_one_of_pos hr
  rw [Real.log_rpow ht] at h2
  rw [abs_le]; constructor <;> nlinarith

theorem solution
    {a : ℝ} (ha : 0 < a) :
    Integrable
      (fun y : ℝ =>
        Real.exp ((-a) * |y|) *
          Real.log
            (lowerCoth (Real.pi * |y| / 2) / (|y| / 2))) := by
  have hpi := Real.pi_pos
  have hg : Integrable (fun y : ℝ =>
      (Real.pi + 2) * (|y| ^ (1:ℝ) * Real.exp (-a * |y|)) +
        (|Real.log Real.pi| + 2 * Real.log 2) * (|y| ^ (0:ℝ) * Real.exp (-a * |y|)) +
        4 * (|y| ^ (-(1/2:ℝ)) * Real.exp (-a * |y|))) := by
    refine (((h47b_rpow_exp (by norm_num) ha).const_mul _).add
      ((h47b_rpow_exp (by norm_num) ha).const_mul _)).add ((h47b_rpow_exp (by norm_num) ha).const_mul _)
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · apply Measurable.aestronglyMeasurable
    unfold lowerCoth
    fun_prop
  · have hE := Real.exp_pos (-a * |y|)
    have hr0 : 0 ≤ |y| ^ (-(1/2:ℝ)) := Real.rpow_nonneg (abs_nonneg y) _
    have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
    rw [Real.rpow_one, Real.rpow_zero, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hE]
    rcases eq_or_ne y 0 with rfl | hy
    · simp [lowerCoth]
      positivity
    have hy0 : 0 < |y| := abs_pos.2 hy
    have hx : 0 < |y| / 2 := by positivity
    have hb := h47b_le hx
    rw [show Real.pi * (|y| / 2) = Real.pi * |y| / 2 by ring] at hb
    have hlx : |Real.log (|y| / 2)| ≤ |y| + 2 * |y| ^ (-(1/2 : ℝ)) + Real.log 2 := by
      rw [Real.log_div hy0.ne' two_ne_zero]
      have := h47b_abslog hy0
      have := abs_sub (Real.log |y|) (Real.log 2)
      rw [abs_of_pos hl2] at this
      linarith
    have : |Real.log (lowerCoth (Real.pi * |y| / 2) / (|y| / 2))| ≤
        (Real.pi + 2) * |y| + (|Real.log Real.pi| + 2 * Real.log 2) + 4 * |y| ^ (-(1/2:ℝ)) := by
      nlinarith
    calc Real.exp (-a * |y|) * |Real.log (lowerCoth (Real.pi * |y| / 2) / (|y| / 2))|
        ≤ Real.exp (-a * |y|) * ((Real.pi + 2) * |y| + (|Real.log Real.pi| + 2 * Real.log 2) + 4 * |y| ^ (-(1/2:ℝ))) :=
          mul_le_mul_of_nonneg_left this hE.le
      _ = _ := by ring

