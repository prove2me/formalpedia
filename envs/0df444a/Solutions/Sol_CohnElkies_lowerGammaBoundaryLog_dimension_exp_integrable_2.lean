-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_dimension_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:11:34.144979+00:00
-- url     : https://prove2.me/submissions/a5df5826-2aa0-4af7-bda0-776b9525ce0d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lower_exp_log_coth_div_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger
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

theorem h47_gamma_shift_prod (z : ℂ) (hz : z.im ≠ 0) (k : ℕ) :
    Complex.Gamma (z + k) = Complex.Gamma z * ∏ j ∈ Finset.range k, (z + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hne : z + (k : ℂ) ≠ 0 := by
      intro h; apply hz; have := congrArg Complex.im h; simpa using this
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, ih, Finset.prod_range_succ]
    ring

theorem h47_int_formula (k : ℕ) (R : ℝ) {y : ℝ} (hy : 0 < y) :
    CohnElkies.lowerGammaBoundaryLog (k : ℝ) R y =
      (k : ℝ) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k, Real.log ‖Complex.I * (y : ℂ) / 2 + (j : ℂ)‖ := by
  unfold CohnElkies.lowerGammaBoundaryLog
  set z : ℂ := Complex.I * (y : ℂ) / 2 with hzdef
  have hzim : z.im = y / 2 := by rw [hzdef]; simp
  have hzim0 : z.im ≠ 0 := by rw [hzim]; positivity
  have hconj : -Complex.I * (y : ℂ) / 2 = starRingEnd ℂ z := by
    rw [hzdef]
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  have h1 : ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ = ‖Complex.Gamma z‖ := by
    rw [hconj, Complex.Gamma_conj, Complex.norm_conj]
  have h2 : (((k : ℝ) : ℂ) + Complex.I * (y : ℂ) / 2) = z + (k : ℂ) := by
    rw [hzdef]; push_cast; ring
  have hG : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm; apply hzim0; rw [hm]; simp
  have hP : ∀ j ∈ Finset.range k, z + (j : ℂ) ≠ 0 := by
    intro j _ h; apply hzim0; have := congrArg Complex.im h; simpa using this
  rw [h1, h2, h47_gamma_shift_prod z hzim0 k, norm_mul, Complex.norm_prod,
    Real.log_mul (norm_ne_zero_iff.mpr hG) (by
      rw [Finset.prod_ne_zero_iff]; intro j hj; exact norm_ne_zero_iff.mpr (hP j hj)),
    Real.log_prod (fun j hj => norm_ne_zero_iff.mpr (hP j hj))]
  ring

theorem h47_harm (d : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R y = lowerGammaBoundaryLog ((d : ℝ) / 2) R |y| := by
  have hc : ∀ s : ℂ, ‖Complex.Gamma ((starRingEnd ℂ) s)‖ = ‖Complex.Gamma s‖ := fun s => by
    rw [Complex.Gamma_conj, Complex.norm_conj]
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    unfold lowerGammaBoundaryLog
    have e1 : -Complex.I * ((-y : ℝ) : ℂ) / 2 = starRingEnd ℂ (-Complex.I * (y : ℂ) / 2) := by
      simp only [map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      push_cast; ring
    have e2 : (((d : ℝ) / 2 : ℝ) : ℂ) + Complex.I * ((-y : ℝ) : ℂ) / 2 =
        starRingEnd ℂ ((((d : ℝ) / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) / 2) := by
      simp only [map_add, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      push_cast; ring
    rw [e1, e2, hc, hc]

theorem h47_bound_int {a : ℝ} (ha : 0 < a) (c₀ c₁ c₂ : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-a * |y|) * (c₀ + c₁ * |y| + c₂ * |y| ^ (-(1/2 : ℝ)))) := by
  have h0 := (h47b_rpow_exp (s := 0) (by norm_num) ha).const_mul c₀
  have h1 := (h47b_rpow_exp (s := 1) (by norm_num) ha).const_mul c₁
  have h2 := (h47b_rpow_exp (s := -(1/2 : ℝ)) (by norm_num) ha).const_mul c₂
  refine ((h0.add h1).add h2).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, Real.rpow_zero, Real.rpow_one]
  ring

theorem h47_ae_ne : ∀ᵐ y : ℝ, y ≠ 0 := by
  rw [MeasureTheory.ae_iff]; simp

theorem h47_logterm_int (j : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => Real.exp (-a * |y|) *
      Real.log ‖Complex.I * ((|y| : ℝ) : ℂ) / 2 + (j : ℂ)‖) := by
  have hmaj := h47_bound_int ha (Real.log 2 + j) 2 2
  have hmeas : Measurable (fun y : ℝ => Real.exp (-a * |y|) *
      Real.log ‖Complex.I * ((|y| : ℝ) : ℂ) / 2 + (j : ℂ)‖) := by fun_prop
  refine hmaj.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [h47_ae_ne] with y hy
  have hyp : 0 < |y| := abs_pos.mpr hy
  have hE := Real.exp_pos (-a * |y|)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE]
  apply mul_le_mul_of_nonneg_left _ hE.le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hab := h47b_abslog hyp
  have hr0 : 0 ≤ |y| ^ (-(1/2 : ℝ)) := Real.rpow_nonneg hyp.le _
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have e : ‖Complex.I * ((|y| : ℝ) : ℂ) / 2 + ((0 : ℕ) : ℂ)‖ = |y| / 2 := by
      simp [abs_of_pos hyp]
    rw [e, Real.log_div hyp.ne' (by norm_num)]
    have := abs_sub (Real.log |y|) (Real.log 2)
    rw [abs_of_pos hl2] at this
    have : (0:ℝ) ≤ 2 * |y| := by positivity
    push_cast
    linarith
  · have hjr : (1:ℝ) ≤ j := by exact_mod_cast hj
    set z : ℂ := Complex.I * ((|y| : ℝ) : ℂ) / 2 + (j : ℂ) with hz
    have hre : z.re = j := by rw [hz]; simp
    have hlow : (1:ℝ) ≤ ‖z‖ := le_trans (by rw [hre]; rw [abs_of_nonneg (by positivity)]; exact hjr)
      (Complex.abs_re_le_norm z)
    have hup : ‖z‖ ≤ |y| / 2 + j := by
      calc ‖z‖ ≤ ‖Complex.I * ((|y| : ℝ) : ℂ) / 2‖ + ‖(j : ℂ)‖ := norm_add_le _ _
        _ = |y| / 2 + j := by simp [abs_of_pos hyp]
    have hl0 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hlow
    have hl1 : Real.log ‖z‖ ≤ ‖z‖ - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [abs_of_nonneg hl0]
    nlinarith

theorem h47_sqrtterm_int (j : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => Real.exp (-a * |y|) *
      Real.log (Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2))) := by
  have hmaj := h47_bound_int ha (Real.log 2 + j + 1) 1 0
  have hmeas : Measurable (fun y : ℝ => Real.exp (-a * |y|) *
      Real.log (Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2))) := by fun_prop
  refine hmaj.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have hE := Real.exp_pos (-a * |y|)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE]
  apply mul_le_mul_of_nonneg_left _ hE.le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set s := Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2) with hs
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hs_low : 1 / 2 ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg (y / 2)]
  have hs_up : s ≤ ((j : ℝ) + 1 / 2) + |y| / 2 := by
    rw [hs, Real.sqrt_le_left (by positivity)]
    have : (y / 2) ^ 2 = (|y| / 2) ^ 2 := by rw [div_pow, div_pow, sq_abs]
    rw [this]; nlinarith [abs_nonneg y]
  have hpos : 0 < s := by linarith
  rcases le_total 1 s with h1 | h1
  · have hl0 : 0 ≤ Real.log s := Real.log_nonneg h1
    have hl1 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hpos
    rw [abs_of_nonneg hl0]
    have : (0:ℝ) ≤ |y| := abs_nonneg y
    linarith
  · have hl0 : Real.log s ≤ 0 := Real.log_nonpos hpos.le h1
    rw [abs_of_nonpos hl0]
    have : Real.log (1 / 2) ≤ Real.log s := Real.log_le_log (by norm_num) hs_low
    rw [one_div, Real.log_inv] at this
    have : (0:ℝ) ≤ |y| := abs_nonneg y
    linarith

theorem solution
    {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryLog ((d : ℝ) / 2) R y) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' d
  · -- integer case
    have hint : Integrable (fun y : ℝ => Real.exp (-a * |y|) * ((k : ℝ) * Real.log (Real.pi * R ^ 2)) -
        ∑ j ∈ Finset.range k, Real.exp (-a * |y|) *
          Real.log ‖Complex.I * ((|y| : ℝ) : ℂ) / 2 + (j : ℂ)‖) :=
      ((h47b_rpow_exp (s := 0) (by norm_num) ha).congr (Filter.Eventually.of_forall fun y => by
          simp) |>.mul_const _).sub (integrable_finset_sum _ fun j _ => h47_logterm_int j ha)
    refine hint.congr ?_
    filter_upwards [h47_ae_ne] with y hy
    have hyp : 0 < |y| := abs_pos.mpr hy
    have e : ((2 * k : ℕ) : ℝ) / 2 = (k : ℝ) := by push_cast; ring
    rw [h47_harm (2 * k) R hy, e, h47_int_formula k R hyp, mul_sub, Finset.mul_sum]
  · -- half-integer case
    have hlcd := CohnElkies.lower_exp_log_coth_div_integrable ha
    have hint : Integrable (fun y : ℝ =>
        Real.exp (-a * |y|) * (((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2)) -
        ∑ j ∈ Finset.range k, Real.exp (-a * |y|) *
          Real.log (Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (1 / 2 : ℝ) * (Real.exp ((-a) * |y|) *
          Real.log (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)))) :=
      ((((h47b_rpow_exp (s := 0) (by norm_num) ha).congr (Filter.Eventually.of_forall fun y => by
          simp)).mul_const _).sub (integrable_finset_sum _ fun j _ => h47_sqrtterm_int j ha)).add
        (hlcd.const_mul _)
    refine hint.congr ?_
    filter_upwards [h47_ae_ne] with y hy
    have e : ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
    rw [e, CohnElkies.lowerGammaBoundaryLog_halfInteger k R hy]
    rw [mul_add, mul_sub, Finset.mul_sum]
    ring

