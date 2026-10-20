-- Prove2me | solution 2 for CohnElkies.lowerCoth_log_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:03:28.635836+00:00
-- url     : https://prove2.me/submissions/6b6f5bda-9033-4c9c-b7c6-c4202710b030

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
theorem h47_int_abs_pow_exp (n : ℕ) {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) := by
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := a)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos ha
  have hIoi : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi 0) := by
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := hx
    simp [abs_of_pos hx0, Real.rpow_natCast]
  have hIio : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iio 0) := by
    have := (show MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi (-0)) by
      simpa using hIoi).comp_neg_Iio
    simpa [abs_neg] using this
  have hall : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iic 0 ∪ Set.Ioi 0) :=
    ((integrableOn_Iic_iff_integrableOn_Iio (b := (0:ℝ))).mpr hIio).union hIoi
  rw [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] at hall
  exact hall

theorem solution :
    Integrable (fun y : ℝ =>
      Real.log (lowerCoth (Real.pi * |y| / 2))) := by
  have hpi := Real.pi_pos
  set g : ℝ → ℝ := fun y => Set.indicator (Set.Icc (-1:ℝ) 1)
      (fun y => Real.pi / 2 + |Real.log (Real.pi / 2)| + |Real.log y|) y +
      4 * (|y| ^ 0 * Real.exp (-(Real.pi / 2) * |y|)) with hg
  have hlog : MeasureTheory.IntegrableOn (fun y : ℝ => Real.pi / 2 + |Real.log (Real.pi / 2)| + |Real.log y|)
      (Set.Icc (-1:ℝ) 1) := by
    have h1 : MeasureTheory.IntegrableOn Real.log (Set.Icc (-1:ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp intervalIntegral.intervalIntegrable_log'
    exact (MeasureTheory.integrableOn_const (by simp)).add h1.abs
  have hgi : Integrable g :=
    (hlog.integrable_indicator measurableSet_Icc).add
      ((h47_int_abs_pow_exp 0 (by positivity : (0:ℝ) < Real.pi / 2)).const_mul 4)
  have hmeas : Measurable (fun y : ℝ => Real.log (lowerCoth (Real.pi * |y| / 2))) := by
    unfold lowerCoth; fun_prop
  refine hgi.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  by_cases hy0 : y = 0
  · subst hy0
    have : lowerCoth (Real.pi * |(0:ℝ)| / 2) = 0 := by simp [lowerCoth]
    rw [this, Real.log_zero, abs_zero]
    rw [hg]; dsimp only
    have h1 : 0 ≤ Set.indicator (Set.Icc (-1:ℝ) 1)
        (fun y => Real.pi / 2 + |Real.log (Real.pi / 2)| + |Real.log y|) 0 :=
      Set.indicator_nonneg (fun _ _ => by positivity) _
    have h2 : 0 ≤ 4 * (|(0:ℝ)| ^ 0 * Real.exp (-(Real.pi / 2) * |(0:ℝ)|)) := by positivity
    linarith
  have hyp : 0 < |y| := abs_pos.mpr hy0
  have hx : 0 < Real.pi * |y| / 2 := by positivity
  set x := Real.pi * |y| / 2 with hxdef
  have hsp : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hcs : Real.sinh x ≤ Real.cosh x := by
    rw [Real.cosh_eq, Real.sinh_eq]; linarith [Real.exp_pos (-x)]
  have hcoth1 : 1 ≤ lowerCoth x := by
    unfold lowerCoth; rw [le_div_iff₀ hsp]; linarith
  have hcpos : 0 < lowerCoth x := by linarith
  have hf0 : 0 ≤ Real.log (lowerCoth x) := Real.log_nonneg hcoth1
  rw [abs_of_nonneg hf0]
  have hind0 : 0 ≤ Set.indicator (Set.Icc (-1:ℝ) 1)
      (fun y => Real.pi / 2 + |Real.log (Real.pi / 2)| + |Real.log y|) y :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  have hE0 : 0 ≤ 4 * (|y| ^ 0 * Real.exp (-(Real.pi / 2) * |y|)) := by positivity
  rw [hg]; dsimp only
  by_cases hsmall : |y| ≤ 1
  · have hmem : y ∈ Set.Icc (-1:ℝ) 1 := abs_le.mp hsmall
    rw [Set.indicator_of_mem hmem]
    have hsinh : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx.le
    have hcosh : Real.cosh x ≤ Real.exp x := by
      rw [Real.cosh_eq]; linarith [Real.exp_le_exp.mpr (show -x ≤ x by linarith)]
    have hcoth : lowerCoth x ≤ Real.exp x / x := by
      unfold lowerCoth
      rw [div_le_div_iff₀ hsp hx]
      nlinarith [Real.cosh_pos x, Real.exp_pos x]
    have h1 : Real.log (lowerCoth x) ≤ x - Real.log x := by
      calc Real.log (lowerCoth x) ≤ Real.log (Real.exp x / x) := Real.log_le_log hcpos hcoth
        _ = x - Real.log x := by rw [Real.log_div (Real.exp_pos x).ne' hx.ne', Real.log_exp]
    have h2 : Real.log x = Real.log (Real.pi / 2) + Real.log |y| := by
      rw [hxdef, show Real.pi * |y| / 2 = Real.pi / 2 * |y| by ring,
        Real.log_mul (by positivity) hyp.ne']
    have h3 : Real.log |y| = Real.log y := Real.log_abs y
    have hxle : x ≤ Real.pi / 2 := by rw [hxdef]; nlinarith
    have h4 := neg_le_abs (Real.log (Real.pi / 2))
    have h5 := neg_le_abs (Real.log y)
    linarith
  · push_neg at hsmall
    have hmem : y ∉ Set.Icc (-1:ℝ) 1 := fun h => by
      have := abs_le.mpr h; linarith
    rw [Set.indicator_of_notMem hmem, zero_add]
    have hx1 : 1 ≤ x := by rw [hxdef]; nlinarith [Real.pi_gt_three]
    -- log coth x ≤ coth x - 1 = e^{-x}/sinh x ≤ 4 e^{-2x} ≤ 4 e^{-x}
    have hl : Real.log (lowerCoth x) ≤ lowerCoth x - 1 := by
      linarith [Real.log_le_sub_one_of_pos hcpos]
    have hEx : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have hEm := Real.exp_pos (-x)
    have hEp := Real.exp_pos x
    have hsinh4 : Real.exp x / 4 ≤ Real.sinh x := by
      rw [Real.sinh_eq]
      have : Real.exp (-x) ≤ Real.exp x / 2 := by
        have h2 : (2:ℝ) ≤ Real.exp x * Real.exp x := by
          have := Real.add_one_le_exp x; nlinarith
        nlinarith
      linarith
    have hcoth_m1 : lowerCoth x - 1 = Real.exp (-x) / Real.sinh x := by
      unfold lowerCoth
      rw [div_sub_one hsp.ne', Real.cosh_sub_sinh]
    have hb : Real.exp (-x) / Real.sinh x ≤ 4 * Real.exp (-x) * Real.exp (-x) := by
      rw [div_le_iff₀ hsp]
      have : 4 * Real.exp (-x) * Real.exp (-x) * Real.sinh x ≥ 4 * Real.exp (-x) * Real.exp (-x) * (Real.exp x / 4) :=
        mul_le_mul_of_nonneg_left hsinh4 (by positivity)
      nlinarith
    have hEle : Real.exp (-x) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    have hfinal : 4 * Real.exp (-x) * Real.exp (-x) ≤ 4 * Real.exp (-x) := by nlinarith
    have hxe : Real.exp (-x) = Real.exp (-(Real.pi / 2) * |y|) := by rw [hxdef]; ring_nf
    rw [pow_zero, one_mul, ← hxe]
    linarith

