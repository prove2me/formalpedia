-- Prove2me | solution 1 for EulerMascheroni.Sondow.remainder_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:55:43.487774+00:00
-- url     : https://prove2.me/submissions/d3c21834-06ba-42c7-b715-d410b51d3eb7

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_eulerMascheroni_sondowCutoff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open MeasureTheory Set intervalIntegral
open EulerMascheroni.Sondow

private noncomputable def kernel (n : ℕ) (x y : ℝ) : ℝ :=
  (x * (1-x) * y * (1-y))^n / ((1-x*y) * (-Real.log (x*y)))

private lemma neg_log_lower {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    2*(1-x)/(1+x) < -Real.log x := by
  have h := Real.lt_log_one_add_of_pos (x := 1/x-1) (by
    rw [sub_pos, one_lt_div hx]; exact hx1)
  have ha : 1 + (1/x-1) = x⁻¹ := by ring
  have hb : 2*(1/x-1)/(1/x-1+2) = 2*(1-x)/(1+x) := by
    apply (div_eq_div_iff (show 1/x-1+2 ≠ 0 by linarith [one_div_pos.mpr hx])
      (show 1+x ≠ 0 by linarith)).mpr
    field_simp; ring
  rwa [ha, hb, Real.log_inv] at h

private lemma kernel_one_lt {x y : ℝ} (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :
    kernel 1 x y < x*y/4 := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hy0 := hy.1
  have hy1 := hy.2
  have ht : 0 < x*y := mul_pos hx.1 hy.1
  have ht1 : x*y < 1 := by nlinarith [mul_pos hx0 (sub_pos.mpr hy1)]
  have hd : 0 < (1-x*y)*(-Real.log (x*y)) :=
    mul_pos (by linarith) (neg_pos.mpr (Real.log_neg ht ht1))
  have hlx := neg_log_lower hx.1 hx.2
  have hly := neg_log_lower hy.1 hy.2
  have hlog : 4*(1-x*y)/((1+x)*(1+y)) < -Real.log (x*y) := by
    rw [Real.log_mul hx.1.ne' hy.1.ne']
    have he : 4*(1-x*y)/((1+x)*(1+y)) =
        2*(1-x)/(1+x)+2*(1-y)/(1+y) := by field_simp [show (1+x) ≠ 0 by linarith, show (1+y) ≠ 0 by linarith]; ring
    rw [he]; linarith
  have hp : 0 < (1+x)*(1+y) := by positivity
  have hm := (div_lt_iff₀ hp).mp hlog
  have hab : 0 < (1-x)*(1-y) := mul_pos (by linarith [hx.2]) (by linarith [hy.2])
  have hs : (1-x*x)*(1-y*y) ≤ (1-x*y)^2 := by nlinarith [sq_nonneg (x-y)]
  have hl : 4*(1-x)*(1-y) < (1-x*y)*(-Real.log (x*y)) := by
    have hmul := mul_lt_mul_of_pos_left hm (show 0 < 1-x*y by linarith)
    nlinarith [mul_nonneg (show 0 ≤ (1+x)*(1+y) by positivity)
      (show 0 ≤ (1-x*y)*(-Real.log (x*y))-4*(1-x)*(1-y) by
        by_contra h; push_neg at h
        have hh := mul_lt_mul_of_pos_right h hp
        nlinarith)]
  unfold kernel
  rw [pow_one, div_lt_iff₀ hd]
  nlinarith [mul_lt_mul_of_pos_left hl ht]

private lemma kernel_bounds (n : ℕ) (hn : 0 < n) {x y : ℝ}
    (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :
    0 < kernel n x y ∧ kernel n x y < (1/16 : ℝ)^(n-1) * (x*y/4) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hy0 := hy.1
  have hy1 := hy.2
  have ht : 0 < x*y := mul_pos hx.1 hy.1
  have ht1 : x*y < 1 := by nlinarith [mul_pos hx0 (sub_pos.mpr hy1)]
  have hb : 0 < x*(1-x)*y*(1-y) := by positivity
  have hd : 0 < (1-x*y)*(-Real.log (x*y)) :=
    mul_pos (by linarith) (neg_pos.mpr (Real.log_neg ht ht1))
  have hbx : x*(1-x) ≤ 1/4 := by nlinarith [sq_nonneg (x-1/2)]
  have hby : y*(1-y) ≤ 1/4 := by nlinarith [sq_nonneg (y-1/2)]
  have hbub : x*(1-x)*y*(1-y) ≤ 1/16 := by nlinarith [mul_le_mul hbx hby (by positivity) (by norm_num)]
  have he : kernel n x y = (x*(1-x)*y*(1-y))^(n-1)*kernel 1 x y := by
    unfold kernel
    rw [pow_one, ← mul_div_assoc, ← pow_succ]
    congr 2; omega
  constructor
  · exact div_pos (pow_pos hb n) hd
  rw [he]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb.le hbub _) (by simpa [kernel] using (div_pos hb hd).le))
    (mul_lt_mul_of_pos_left (kernel_one_lt hx hy) (by positivity))

private lemma unit_integrable {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ x ∈ Ioo (0:ℝ) 1, ‖f x‖ ≤ C) : IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
  exact Measure.integrableOn_of_bounded (by simp) hf.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall hb))

private lemma unit_integral_lt {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    (h : ∀ x ∈ Ioo (0:ℝ) 1, f x < g x) :
    (∫ x in (0:ℝ)..1, f x) < ∫ x in (0:ℝ)..1, g x := by
  have hh := intervalIntegral.intervalIntegral_pos_of_pos_on (hg.sub hf)
    (fun x hx => sub_pos.mpr (h x hx)) (by norm_num : (0:ℝ)<1)
  rw [integral_sub hg hf] at hh
  linarith

private lemma kernel_measurable (n : ℕ) : Measurable (fun p : ℝ × ℝ => kernel n p.1 p.2) := by
  unfold kernel
  fun_prop

private lemma kernel_inner_integrable (n : ℕ) (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Ioo 0 1) : IntervalIntegrable (kernel n x) volume 0 1 := by
  apply unit_integrable ((kernel_measurable n).comp (measurable_const.prodMk measurable_id))
    (C := (1/16:ℝ)^(n-1)/4)
  intro y hy
  obtain ⟨hp, hu⟩ := kernel_bounds n hn hx hy
  change ‖kernel n x y‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos hp]
  have ht : x*y ≤ 1 := by nlinarith [mul_pos hx.1 (sub_pos.mpr hy.2), hx.2]
  nlinarith [mul_le_mul_of_nonneg_left ht (show 0 ≤ (1/16:ℝ)^(n-1) by positivity)]

private lemma kernel_inner_bounds (n : ℕ) (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Ioo 0 1) :
    0 < (∫ y in (0:ℝ)..1, kernel n x y) ∧
      (∫ y in (0:ℝ)..1, kernel n x y) < (1/16:ℝ)^(n-1)*x/8 := by
  have hi := kernel_inner_integrable n hn hx
  constructor
  · exact intervalIntegral_pos_of_pos_on hi (fun y hy => (kernel_bounds n hn hx hy).1) (by norm_num)
  have hu := unit_integral_lt hi
    (show IntervalIntegrable (fun y => (1/16:ℝ)^(n-1)*(x*y/4)) volume 0 1 from by
      apply Continuous.intervalIntegrable; fun_prop)
    (fun y hy => (kernel_bounds n hn hx hy).2)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, integral_id] at hu
  norm_num at hu
  convert hu using 1 <;> ring

private lemma kernel_outer_measurable (n : ℕ) :
    Measurable (fun x => ∫ y in (0:ℝ)..1, kernel n x y) := by
  simp_rw [integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  exact (kernel_measurable n).stronglyMeasurable.integral_prod_right'.measurable

open Filter
open scoped Topology

private lemma power_kernel_bounds (n : ℕ) (hn : 0 < n) (N : ℕ) {x y : ℝ}
    (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :
    0 ≤ kernel n x y * (x*y)^N ∧ kernel n x y * (x*y)^N ≤ kernel n x y := by
  have hp := (kernel_bounds n hn hx hy).1.le
  have ht : x*y ≤ 1 := by nlinarith [mul_pos hx.1 (sub_pos.mpr hy.2), hx.2]
  exact ⟨mul_nonneg hp (pow_nonneg (mul_pos hx.1 hy.1).le _),
    mul_le_of_le_one_right hp (pow_le_one₀ (mul_pos hx.1 hy.1).le ht)⟩

private lemma power_kernel_measurable (n N : ℕ) :
    Measurable (fun p : ℝ × ℝ => kernel n p.1 p.2 * (p.1*p.2)^N) := by
  exact (kernel_measurable n).mul (by fun_prop)

private lemma power_inner_integrable (n : ℕ) (hn : 0 < n) (N : ℕ) {x : ℝ}
    (hx : x ∈ Ioo 0 1) :
    IntervalIntegrable (fun y => kernel n x y * (x*y)^N) volume 0 1 := by
  apply unit_integrable ((power_kernel_measurable n N).comp (measurable_const.prodMk measurable_id))
    (C := (1/16:ℝ)^(n-1)/4)
  intro y hy
  change ‖kernel n x y * (x*y)^N‖ ≤ _
  obtain ⟨hp, hu⟩ := power_kernel_bounds n hn N hx hy
  rw [Real.norm_eq_abs, abs_of_nonneg hp]
  have hb := (kernel_bounds n hn hx hy).2
  have ht : x*y ≤ 1 := by nlinarith [mul_pos hx.1 (sub_pos.mpr hy.2), hx.2]
  nlinarith [mul_le_mul_of_nonneg_left ht (show 0 ≤ (1/16:ℝ)^(n-1) by positivity)]

private lemma power_inner_tendsto (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    Tendsto (fun N : ℕ => ∫ y in (0:ℝ)..1, kernel n x y*(x*y)^N) atTop (𝓝 0) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (l := atTop) (μ := volume) (a := (0:ℝ)) (b := 1)
    (F := fun N : ℕ => fun y => kernel n x y*(x*y)^N) (f := fun _ => (0:ℝ))
    (kernel n x) ?_ ?_ (kernel_inner_integrable n hn hx) ?_
  · simpa using h
  · exact Eventually.of_forall fun N =>
      ((power_kernel_measurable n N).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun N => ?_
    filter_upwards [volume.ae_ne (1:ℝ)] with y hyne hy
    rw [uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hy
    have hy' : y ∈ Ioo 0 1 := ⟨hy.1, lt_of_le_of_ne hy.2 hyne⟩
    obtain ⟨hp, hu⟩ := power_kernel_bounds n hn N hx hy'
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    exact hu
  · filter_upwards [volume.ae_ne (1:ℝ)] with y hyne hy
    rw [uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hy
    have ht : x*y < 1 := by nlinarith [mul_pos hx.1 (sub_pos.mpr (lt_of_le_of_ne hy.2 hyne)), hx.2]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_pos hx.1 hy.1).le ht).const_mul (kernel n x y)

theorem solution (n : ℕ) (hn : 0 < n) :
    Tendsto (remainder n) atTop (𝓝 0) := by
  have hi : IntervalIntegrable (fun x => ∫ y in (0:ℝ)..1, kernel n x y) volume 0 1 := by
    apply unit_integrable (kernel_outer_measurable n) (C := (1/16:ℝ)^(n-1)/8)
    intro x hx
    obtain ⟨hp, hu⟩ := kernel_inner_bounds n hn hx
    rw [Real.norm_eq_abs, abs_of_pos hp]
    nlinarith [mul_le_mul_of_nonneg_left hx.2.le (show 0 ≤ (1/16:ℝ)^(n-1) by positivity)]
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (l := atTop) (μ := volume) (a := (0:ℝ)) (b := 1)
    (F := fun N : ℕ => fun x => ∫ y in (0:ℝ)..1, kernel n x y*(x*y)^N)
    (f := fun _ => (0:ℝ)) (fun x => ∫ y in (0:ℝ)..1, kernel n x y) ?_ ?_ hi ?_
  · change Tendsto (fun N => remainder n N) atTop (𝓝 0)
    simpa only [remainder, kernel, intervalIntegral.integral_zero] using h
  · refine Eventually.of_forall fun N => ?_
    simp_rw [integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
    exact (power_kernel_measurable n N).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  · refine Eventually.of_forall fun N => ?_
    filter_upwards [volume.ae_ne (1:ℝ)] with x hxne hx
    rw [uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hx
    have hx' : x ∈ Ioo 0 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hxne⟩
    have hpos : 0 ≤ ∫ y in (0:ℝ)..1, kernel n x y*(x*y)^N := by
      have hh := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ) ≤ 1)
        (intervalIntegrable_const (c := (0:ℝ))) (power_inner_integrable n hn N hx')
        (fun y hy => (power_kernel_bounds n hn N hx' hy).1)
      simpa using hh
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    exact intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      (power_inner_integrable n hn N hx') (kernel_inner_integrable n hn hx')
      (fun y hy => (power_kernel_bounds n hn N hx' hy).2)
  · filter_upwards [volume.ae_ne (1:ℝ)] with x hxne hx
    rw [uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hx
    exact power_inner_tendsto n hn ⟨hx.1, lt_of_le_of_ne hx.2 hxne⟩

#print axioms solution



