-- Prove2me | solution 1 for DerivativeChainPrivate.continuousTrinomialBranch
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T07:40:55.372481+00:00
-- url     : https://prove2.me/submissions/430c39f6-0efe-4022-8c95-4e722742adac

import Definitions.Def_DerivativeChainPrivate_foundations
open Filter Topology
open scoped BigOperators
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false



set_option autoImplicit false
namespace DerivativeChainPrivate



theorem trinomial_root_locus_scalar_positive (h p q : ℝ)
    (hh : 1 < h) (hpq : 0 < p + q) :
    0 < p + h ^ 2 * q - (h - 1) ^ 2 * ((p * q - 1) / (p + q)) := by
  have heq : p + h ^ 2 * q - (h - 1) ^ 2 * ((p * q - 1) / (p + q)) =
      ((p + h * q) ^ 2 + (h - 1) ^ 2) / (p + q) := by
    field_simp
    ring
  rw [heq]
  apply div_pos _ hpq
  have hsq : 0 < (h - 1) ^ 2 := sq_pos_of_pos (by linarith)
  nlinarith [sq_nonneg (p + h * q)]

end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate

theorem sine_triangle_root_curve (B theta : ℝ) (hB : Real.sin B ≠ 0) :
    ((Real.sin (B + theta) / Real.sin B : ℝ) : ℂ) *
        Complex.exp ((theta : ℂ) * Complex.I) - 1 =
      ((Real.sin theta / Real.sin B : ℝ) : ℂ) *
        Complex.exp (((B + theta : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero]
  · rw [Real.sin_add, Real.cos_add]
    field_simp [hB]
    linear_combination (Real.sin B) * Real.sin_sq_add_cos_sq theta
  · rw [Real.sin_add]
    ring

theorem trinomial_angle_slope_positive (h theta B : ℝ) (hh : 1 < h)
    (htheta : 0 < theta) (hB : 0 < B) (hangle : theta + B < Real.pi) :
    0 < Real.cot theta + h ^ 2 * Real.cot B -
      (h - 1) ^ 2 * Real.cot (theta + B) := by
  have hst := Real.sin_pos_of_pos_of_lt_pi htheta (by linarith)
  have hsb := Real.sin_pos_of_pos_of_lt_pi hB (by linarith)
  have hsa := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < theta + B) hangle
  have hsum : Real.cot theta + Real.cot B =
      Real.sin (theta + B) / (Real.sin theta * Real.sin B) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.sin_add]
    field_simp
    ring
  have hsumpos : 0 < Real.cot theta + Real.cot B := by
    rw [hsum]
    exact div_pos hsa (mul_pos hst hsb)
  have hcot : Real.cot (theta + B) =
      (Real.cot theta * Real.cot B - 1) / (Real.cot theta + Real.cot B) := by
    rw [hsum]
    simp only [Real.cot_eq_cos_div_sin]
    field_simp [hst.ne', hsb.ne', hsa.ne']
    rw [Real.cos_add]
  rw [hcot]
  exact trinomial_root_locus_scalar_positive h (Real.cot theta) (Real.cot B) hh hsumpos

noncomputable def trinomialLogParameter (psi h theta : ℝ) : ℝ :=
  (h - 1) * Real.log (Real.sin (psi - (h - 1) * theta)) + Real.log (Real.sin theta) -
    h * Real.log (Real.sin (psi - h * theta))

theorem trinomial_log_parameter_hasDerivAt (psi h theta : ℝ)
    (hA : Real.sin (psi - (h - 1) * theta) ≠ 0)
    (hB : Real.sin (psi - h * theta) ≠ 0) (ht : Real.sin theta ≠ 0) :
    HasDerivAt (trinomialLogParameter psi h)
      (Real.cot theta + h ^ 2 * Real.cot (psi - h * theta) -
        (h - 1) ^ 2 * Real.cot (psi - (h - 1) * theta)) theta := by
  have ha : HasDerivAt (fun t : ℝ => psi - (h - 1) * t) (-(h - 1)) theta := by
    convert! ((hasDerivAt_id theta).const_mul (h - 1)).const_sub psi using 1
    ring
  have hb : HasDerivAt (fun t : ℝ => psi - h * t) (-h) theta := by
    convert! ((hasDerivAt_id theta).const_mul h).const_sub psi using 1
    ring
  have hloga := (Real.hasDerivAt_log hA).comp theta
    ((Real.hasDerivAt_sin (psi - (h - 1) * theta)).comp theta ha)
  have hlogb := (Real.hasDerivAt_log hB).comp theta
    ((Real.hasDerivAt_sin (psi - h * theta)).comp theta hb)
  have hlogt := (Real.hasDerivAt_log ht).comp theta (Real.hasDerivAt_sin theta)
  convert! ((hloga.const_mul (h - 1)).add hlogt).sub (hlogb.const_mul h) using 1
  simp only [Real.cot_eq_cos_div_sin, div_eq_mul_inv]
  ring

theorem trinomial_log_parameter_strictMonoOn (psi h : ℝ) (_hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) :
    StrictMonoOn (trinomialLogParameter psi h) (Set.Ioo 0 (psi / h)) := by
  have hh0 : 0 < h := by linarith
  have hdata (theta : ℝ) (ht : theta ∈ Set.Ioo 0 (psi / h)) :
      HasDerivAt (trinomialLogParameter psi h)
        (Real.cot theta + h ^ 2 * Real.cot (psi - h * theta) -
          (h - 1) ^ 2 * Real.cot (psi - (h - 1) * theta)) theta ∧
      0 < Real.cot theta + h ^ 2 * Real.cot (psi - h * theta) -
          (h - 1) ^ 2 * Real.cot (psi - (h - 1) * theta) := by
    have hB : 0 < psi - h * theta := by
      have hmul := (lt_div_iff₀ hh0).mp ht.2
      nlinarith
    have hAeq : psi - (h - 1) * theta = theta + (psi - h * theta) := by ring
    have hA : 0 < psi - (h - 1) * theta := by rw [hAeq]; linarith [ht.1]
    have hApi : theta + (psi - h * theta) < Real.pi := by nlinarith [ht.1]
    have hst := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith)
    have hsB := Real.sin_pos_of_pos_of_lt_pi hB (by linarith [ht.1])
    have hsA := Real.sin_pos_of_pos_of_lt_pi hA (by rw [hAeq]; exact hApi)
    refine ⟨trinomial_log_parameter_hasDerivAt psi h theta hsA.ne' hsB.ne' hst.ne', ?_⟩
    rw [hAeq]
    exact trinomial_angle_slope_positive h theta (psi - h * theta) hh ht.1 hB hApi
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro theta ht
    exact ((hdata theta ht).1).continuousAt.continuousWithinAt
  · intro theta ht
    rw [interior_Ioo] at ht
    rw [((hdata theta ht).1).deriv]
    exact (hdata theta ht).2

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace DerivativeChainPrivate

noncomputable def trinomialParameter (psi h theta : ℝ) : ℝ :=
  Real.sin (psi - (h - 1) * theta) ^ (h - 1) * Real.sin theta /
    Real.sin (psi - h * theta) ^ h

theorem trinomial_parameter_sines (psi h theta : ℝ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) (ht : theta ∈ Ioo 0 (psi / h)) :
    0 < Real.sin (psi - (h - 1) * theta) ∧ 0 < Real.sin theta ∧
      0 < Real.sin (psi - h * theta) := by
  have hh0 : 0 < h := by linarith
  have hB : 0 < psi - h * theta := by
    have := (lt_div_iff₀ hh0).mp ht.2
    nlinarith
  have hA : 0 < psi - (h - 1) * theta := by nlinarith [ht.1]
  refine ⟨Real.sin_pos_of_pos_of_lt_pi hA (by nlinarith [ht.1]),
    Real.sin_pos_of_pos_of_lt_pi ht.1 (by nlinarith [ht.1]),
    Real.sin_pos_of_pos_of_lt_pi hB (by nlinarith [ht.1])⟩

theorem trinomial_parameter_pos (psi h theta : ℝ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) (ht : theta ∈ Ioo 0 (psi / h)) :
    0 < trinomialParameter psi h theta := by
  obtain ⟨hA, ht, hB⟩ := trinomial_parameter_sines psi h theta hpsi hpi hh ht
  exact div_pos (mul_pos (Real.rpow_pos_of_pos hA _) ht) (Real.rpow_pos_of_pos hB _)

theorem trinomial_parameter_log (psi h theta : ℝ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) (ht : theta ∈ Ioo 0 (psi / h)) :
    Real.log (trinomialParameter psi h theta) = trinomialLogParameter psi h theta := by
  obtain ⟨hA, ht, hB⟩ := trinomial_parameter_sines psi h theta hpsi hpi hh ht
  rw [trinomialParameter, Real.log_div
    (mul_ne_zero (Real.rpow_pos_of_pos hA _).ne' ht.ne')
    (Real.rpow_pos_of_pos hB _).ne', Real.log_mul (Real.rpow_pos_of_pos hA _).ne' ht.ne',
    Real.log_rpow hA, Real.log_rpow hB]
  rfl

theorem trinomial_parameter_strictMonoOn (psi h : ℝ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) :
    StrictMonoOn (trinomialParameter psi h) (Ioo 0 (psi / h)) := by
  intro x hx y hy hxy
  have hlog := trinomial_log_parameter_strictMonoOn psi h hpsi hpi hh hx hy hxy
  rw [← trinomial_parameter_log psi h x hpsi hpi hh hx,
    ← trinomial_parameter_log psi h y hpsi hpi hh hy] at hlog
  exact (Real.log_lt_log_iff (trinomial_parameter_pos psi h x hpsi hpi hh hx)
    (trinomial_parameter_pos psi h y hpsi hpi hh hy)).mp hlog

theorem trinomial_parameter_exists (psi h T : ℝ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) (hT : 0 < T) :
    ∃ theta ∈ Ioo 0 (psi / h), trinomialParameter psi h theta = T := by
  have hh0 : 0 < h := by linarith
  have hU : 0 < psi / h := div_pos hpsi hh0
  have hUpsi : psi / h < psi := (div_lt_self hpsi hh).trans_le (le_refl psi)
  have hspsi := Real.sin_pos_of_pos_of_lt_pi hpsi hpi
  have hsU := Real.sin_pos_of_pos_of_lt_pi hU (hUpsi.trans hpi)
  let G (theta : ℝ) :=
    Real.sin (psi - (h - 1) * theta) ^ (h - 1) * Real.sin theta -
      T * Real.sin (psi - h * theta) ^ h
  have hcontA : Continuous (fun theta : ℝ => Real.sin (psi - (h - 1) * theta)) := by fun_prop
  have hcontB : Continuous (fun theta : ℝ => Real.sin (psi - h * theta)) := by fun_prop
  have hc : Continuous G :=
    (((Real.continuous_rpow_const (by linarith : 0 ≤ h - 1)).comp hcontA).mul
      Real.continuous_sin).sub
      (continuous_const.mul ((Real.continuous_rpow_const hh0.le).comp hcontB))
  have hG0 : G 0 < 0 := by
    dsimp [G]
    simp only [mul_zero, sub_zero, Real.sin_zero, zero_sub]
    exact neg_neg_of_pos (mul_pos hT (Real.rpow_pos_of_pos hspsi h))
  have hBA : psi - h * (psi / h) = 0 := by field_simp; ring
  have hAA : psi - (h - 1) * (psi / h) = psi / h := by field_simp; ring
  have hGU : 0 < G (psi / h) := by
    dsimp [G]
    rw [hBA, hAA, Real.sin_zero, Real.zero_rpow (ne_of_gt hh0), mul_zero, sub_zero]
    exact mul_pos (Real.rpow_pos_of_pos hsU _) hsU
  obtain ⟨theta, ht, hzero⟩ := intermediate_value_Ioo hU.le hc.continuousOn ⟨hG0, hGU⟩
  refine ⟨theta, ht, ?_⟩
  obtain ⟨hA, hst, hB⟩ := trinomial_parameter_sines psi h theta hpsi hpi hh ht
  apply (div_eq_iff (Real.rpow_pos_of_pos hB h).ne').mpr
  exact sub_eq_zero.mp hzero



theorem trinomial_parameter_image (psi h : ℝ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) :
    trinomialParameter psi h '' Ioo 0 (psi / h) = Ioi 0 := by
  ext T
  constructor
  · rintro ⟨theta, ht, rfl⟩
    exact trinomial_parameter_pos psi h theta hpsi hpi hh ht
  · intro hT
    exact trinomial_parameter_exists psi h T hpsi hpi hh hT

noncomputable def trinomialParameterIso (psi h : ℝ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) :
    Ioo (0 : ℝ) (psi / h) ≃o Ioi (0 : ℝ) :=
  (StrictMonoOn.orderIso (trinomialParameter psi h) (Ioo 0 (psi / h))
    (trinomial_parameter_strictMonoOn psi h hpsi hpi hh)).trans
      (OrderIso.setCongr _ _ (trinomial_parameter_image psi h hpsi hpi hh))

theorem trinomial_angle_inverse_value (psi h : ℝ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) (T : Ioi (0 : ℝ)) :
    trinomialParameter psi h ((trinomialParameterIso psi h hpsi hpi hh).symm T) = T := by
  exact congrArg Subtype.val ((trinomialParameterIso psi h hpsi hpi hh).apply_symm_apply T)

theorem trinomial_angle_inverse_continuous (psi h : ℝ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) :
    Continuous (fun T : Ioi (0 : ℝ) =>
      (((trinomialParameterIso psi h hpsi hpi hh).symm T) : ℝ)) :=
  continuous_subtype_val.comp (trinomialParameterIso psi h hpsi hpi hh).symm.continuous

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate

noncomputable def trinomialCurveRoot (psi h theta : ℝ) (d : ℕ) : ℂ :=
  Complex.exp (((Real.log (Real.sin (psi - (h - 1) * theta) /
    Real.sin (psi - h * theta)) / d : ℝ) : ℂ) + ((theta / d : ℝ) : ℂ) * Complex.I)

theorem polar_exponential_pow (L theta : ℝ) (n : ℕ) :
    (Complex.exp ((L : ℂ) + (theta : ℂ) * Complex.I)) ^ n =
      Complex.exp ((((n : ℝ) * L : ℝ) : ℂ) +
        (((n : ℝ) * theta : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem trinomial_curve_power (psi h theta : ℝ) (d : ℕ) (hd : 0 < d)
    (hrho : 0 < Real.sin (psi - (h - 1) * theta) / Real.sin (psi - h * theta)) :
    (trinomialCurveRoot psi h theta d) ^ d =
      ((Real.sin (psi - (h - 1) * theta) / Real.sin (psi - h * theta) : ℝ) : ℂ) *
        Complex.exp ((theta : ℂ) * Complex.I) := by
  let rho := Real.sin (psi - (h - 1) * theta) / Real.sin (psi - h * theta)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hdL : (d : ℝ) * (Real.log rho / d) = Real.log rho := by field_simp
  have hdtheta : (d : ℝ) * (theta / d) = theta := by field_simp
  change (Complex.exp (((Real.log rho / d : ℝ) : ℂ) +
    ((theta / d : ℝ) : ℂ) * Complex.I)) ^ d = _
  rw [polar_exponential_pow, hdL, hdtheta, Complex.exp_add,
    ← Complex.ofReal_exp, Real.exp_log hrho]

theorem trinomial_curve_equation (d e : ℕ) (hd : 0 < d) (hde : d < e)
    (psi theta : ℝ) (hpsi : 0 < psi) (hpi : psi < Real.pi)
    (ht : theta ∈ Set.Ioo 0 (psi / ((e : ℝ) / d))) :
    (trinomialCurveRoot psi ((e : ℝ) / d) theta d) ^ (e - d) *
      ((trinomialCurveRoot psi ((e : ℝ) / d) theta d) ^ d - 1) =
        (trinomialParameter psi ((e : ℝ) / d) theta : ℂ) *
          Complex.exp ((psi : ℂ) * Complex.I) := by
  let h : ℝ := (e : ℝ) / d
  let A : ℝ := psi - (h - 1) * theta
  let B : ℝ := psi - h * theta
  let rho : ℝ := Real.sin A / Real.sin B
  let s : ℝ := Real.sin theta / Real.sin B
  let L : ℝ := Real.log rho / d
  let phi : ℝ := theta / d
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := hdpos.ne'
  have hh : 1 < h := (one_lt_div hdpos).mpr (by exact_mod_cast hde)
  obtain ⟨hA, htheta, hB⟩ := trinomial_parameter_sines psi h theta hpsi hpi hh ht
  have hrho : 0 < rho := div_pos hA hB
  have hs : 0 < s := div_pos htheta hB
  have hroot : trinomialCurveRoot psi h theta d =
      Complex.exp ((L : ℂ) + (phi : ℂ) * Complex.I) := rfl
  have hxpow : (trinomialCurveRoot psi h theta d) ^ d =
      (rho : ℂ) * Complex.exp ((theta : ℂ) * Complex.I) := by
    exact trinomial_curve_power psi h theta d hd hrho
  have hsine : (rho : ℂ) * Complex.exp ((theta : ℂ) * Complex.I) - 1 =
      (s : ℂ) * Complex.exp ((A : ℂ) * Complex.I) := by
    have heq : B + theta = A := by dsimp [A, B]; ring
    simpa only [heq] using sine_triangle_root_curve B theta hB.ne'
  have hsExp : (s : ℂ) * Complex.exp ((A : ℂ) * Complex.I) =
      Complex.exp (((Real.log s : ℝ) : ℂ) + (A : ℂ) * Complex.I) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hs]
  have hlong : (trinomialCurveRoot psi h theta d) ^ (e - d) =
      Complex.exp (((((e - d : ℕ) : ℝ) * L : ℝ) : ℂ) +
        (((((e - d : ℕ) : ℝ) * phi) : ℝ) : ℂ) * Complex.I) := by
    rw [hroot, polar_exponential_pow]
  have hreal : ((e - d : ℕ) : ℝ) * L + Real.log s =
      Real.log (trinomialParameter psi h theta) := by
    rw [trinomial_parameter_log psi h theta hpsi hpi hh ht]
    change ((e - d : ℕ) : ℝ) * (Real.log (Real.sin A / Real.sin B) / d) +
      Real.log (Real.sin theta / Real.sin B) =
        (h - 1) * Real.log (Real.sin A) + Real.log (Real.sin theta) - h * Real.log (Real.sin B)
    rw [Real.log_div hA.ne' hB.ne', Real.log_div htheta.ne' hB.ne']
    have halgebra (a b c : ℝ) : ((e - d : ℕ) : ℝ) * ((a - b) / d) + (c - b) =
        (h - 1) * a + c - h * b := by
      rw [Nat.cast_sub hde.le]
      dsimp only [h]
      field_simp
      ring
    exact halgebra _ _ _
  have himag : ((e - d : ℕ) : ℝ) * phi + A = psi := by
    dsimp [phi, A, h]
    rw [Nat.cast_sub hde.le]
    field_simp
    ring
  have hparameter := trinomial_parameter_pos psi h theta hpsi hpi hh ht
  have hparameterExp : Complex.exp (((Real.log (trinomialParameter psi h theta) : ℝ) : ℂ)) =
      (trinomialParameter psi h theta : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hparameter]
  change (trinomialCurveRoot psi h theta d) ^ (e - d) *
    ((trinomialCurveRoot psi h theta d) ^ d - 1) = _
  rw [hlong, hxpow, hsine, hsExp, ← Complex.exp_add, ← hparameterExp, ← Complex.exp_add]
  congr 1
  calc
    _ = (((((e - d : ℕ) : ℝ) * L + Real.log s : ℝ) : ℂ)) +
        (((((e - d : ℕ) : ℝ) * phi + A : ℝ) : ℂ)) * Complex.I := by push_cast; ring
    _ = _ := by rw [hreal, himag]



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace DerivativeChainPrivate

theorem continuousOn_trinomialCurveRoot (psi h : ℝ) (d : ℕ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) :
    ContinuousOn (fun theta => trinomialCurveRoot psi h theta d) (Ioo 0 (psi / h)) := by
  intro theta ht
  obtain ⟨hA, htheta, hB⟩ := trinomial_parameter_sines psi h theta hpsi hpi hh ht
  have hAc : ContinuousAt (fun t : ℝ => Real.sin (psi - (h - 1) * t)) theta := by fun_prop
  have hBc : ContinuousAt (fun t : ℝ => Real.sin (psi - h * t)) theta := by fun_prop
  have hrho : ContinuousAt (fun t : ℝ => Real.sin (psi - (h - 1) * t) /
      Real.sin (psi - h * t)) theta := hAc.div hBc hB.ne'
  have hlog : ContinuousAt (fun t : ℝ => Real.log (Real.sin (psi - (h - 1) * t) /
      Real.sin (psi - h * t))) theta :=
    ContinuousAt.comp (f := fun t : ℝ => Real.sin (psi - (h - 1) * t) /
      Real.sin (psi - h * t)) (x := theta)
      (Real.continuousAt_log (div_pos hA hB).ne') hrho
  have hL : ContinuousAt (fun t : ℝ => Real.log (Real.sin (psi - (h - 1) * t) /
      Real.sin (psi - h * t)) / d) theta := hlog.div_const (d : ℝ)
  have hphi := (continuousAt_id (x := theta)).div_const (d : ℝ)
  have hcomplex := (Complex.continuous_ofReal.continuousAt.comp hL).add
    ((Complex.continuous_ofReal.continuousAt.comp hphi).mul (continuousAt_const (y := Complex.I)))
  exact (Complex.continuous_exp.continuousAt.comp hcomplex).continuousWithinAt

noncomputable def trinomialPositiveBranch (psi h : ℝ) (d : ℕ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) (T : Ioi (0 : ℝ)) : ℂ :=
  trinomialCurveRoot psi h ((trinomialParameterIso psi h hpsi hpi hh).symm T) d

theorem continuous_trinomialPositiveBranch (psi h : ℝ) (d : ℕ) (hpsi : 0 < psi)
    (hpi : psi < Real.pi) (hh : 1 < h) :
    Continuous (trinomialPositiveBranch psi h d hpsi hpi hh) := by
  exact (continuousOn_trinomialCurveRoot psi h d hpsi hpi hh).comp_continuous
    (trinomial_angle_inverse_continuous psi h hpsi hpi hh)
    (fun T => ((trinomialParameterIso psi h hpsi hpi hh).symm T).property)

theorem trinomial_positive_branch_equation (d e : ℕ) (hd : 0 < d) (hde : d < e)
    (psi : ℝ) (hpsi : 0 < psi) (hpi : psi < Real.pi)
    (hh : 1 < (e : ℝ) / d) (T : Ioi (0 : ℝ)) :
    (trinomialPositiveBranch psi ((e : ℝ) / d) d hpsi hpi hh T) ^ (e - d) *
      ((trinomialPositiveBranch psi ((e : ℝ) / d) d hpsi hpi hh T) ^ d - 1) =
        (T : ℂ) * Complex.exp ((psi : ℂ) * Complex.I) := by
  unfold trinomialPositiveBranch
  rw [trinomial_curve_equation d e hd hde psi _ hpsi hpi
    (((trinomialParameterIso psi ((e : ℝ) / d) hpsi hpi hh).symm T).property),
    trinomial_angle_inverse_value]

theorem trinomial_curve_power_im_pos (psi h theta : ℝ) (d : ℕ) (hd : 0 < d)
    (hpsi : 0 < psi) (hpi : psi < Real.pi) (hh : 1 < h)
    (ht : theta ∈ Ioo 0 (psi / h)) :
    0 < ((trinomialCurveRoot psi h theta d) ^ d).im := by
  obtain ⟨hA, htheta, hB⟩ := trinomial_parameter_sines psi h theta hpsi hpi hh ht
  rw [trinomial_curve_power psi h theta d hd (div_pos hA hB)]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
  exact mul_pos (div_pos hA hB) htheta

theorem trinomial_derivative_ne_zero (d e : ℕ) (hde : d < e) (c x : ℂ)
    (hx : x ≠ 0) (him : 0 < (x ^ d).im) :
    (Polynomial.X ^ e - Polynomial.X ^ (e - d) - Polynomial.C c).derivative.eval x ≠ 0 := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hexp : e - 1 = e - d - 1 + d := by omega
  have hform : (Polynomial.X ^ e - Polynomial.X ^ (e - d) - Polynomial.C c).derivative.eval x =
      x ^ (e - d - 1) * ((e : ℂ) * x ^ d - ((e - d : ℕ) : ℂ)) := by
    simp only [Polynomial.derivative_sub, Polynomial.derivative_pow, Polynomial.derivative_X,
      Polynomial.derivative_C, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X,
      mul_one, sub_zero]
    rw [hexp, pow_add]
    ring
  rw [hform]
  apply mul_ne_zero (pow_ne_zero _ hx)
  intro h
  have hzero : (e : ℝ) * (x ^ d).im = 0 := by
    simpa using congrArg Complex.im h
  exact (ne_of_gt (mul_pos he0 him)) hzero

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (d e : ℕ) (hd : 0 < d) (hde : d < e)
    (psi : ℝ) (hpsi : 0 < psi) (hpi : psi < Real.pi) :
    ∃ f : Set.Ioi (0 : ℝ) → ℂ, Continuous f ∧ ∀ T,
      f T ^ (e - d) * (f T ^ d - 1) =
        (T : ℂ) * Complex.exp ((psi : ℂ) * Complex.I) ∧
      f T ≠ 0 ∧
      (Polynomial.X ^ e - Polynomial.X ^ (e - d) -
        Polynomial.C ((T : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))).derivative.eval (f T) ≠ 0 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hh : 1 < (e : ℝ) / d := (one_lt_div hdpos).mpr (by exact_mod_cast hde)
  let f := trinomialPositiveBranch psi ((e : ℝ) / d) d hpsi hpi hh
  refine ⟨f, continuous_trinomialPositiveBranch psi ((e : ℝ) / d) d hpsi hpi hh, ?_⟩
  intro T
  have hroot := trinomial_positive_branch_equation d e hd hde psi hpsi hpi hh T
  have hnonzero : f T ≠ 0 := by
    change Complex.exp _ ≠ 0
    exact Complex.exp_ne_zero _
  have him : 0 < ((f T) ^ d).im := by
    exact trinomial_curve_power_im_pos psi ((e : ℝ) / d) _ d hd hpsi hpi hh
      (((trinomialParameterIso psi ((e : ℝ) / d) hpsi hpi hh).symm T).property)
  exact ⟨hroot, hnonzero, trinomial_derivative_ne_zero d e hde _ _ hnonzero him⟩
