-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_remainder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:30:48.557627+00:00
-- url     : https://prove2.me/submissions/cbdd7939-eb26-49a5-91c5-db094e682a7f

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthOcticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_coefficient_bounds
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_real_positive
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_tail_deriv_bound
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_tail_differentiableAt
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_tail_imaginary_axis
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem analytic_error_coordinate_bounds (E : ℂ → ℂ) (R δ : ℝ)
    (hdiff : ∀ v : ℂ, ‖v‖^2 ≤ R → DifferentiableAt ℂ E v)
    (hderiv : ∀ v : ℂ, ‖v‖^2 ≤ R → ‖deriv E v‖ ≤ δ)
    (haxes : ∀ x : ℝ, x^2 ≤ R → (E (x:ℂ)).im=0 ∧ (E (Complex.I*(x:ℂ))).re=0)
    (w : ℂ) (hw : ‖w‖^2 ≤ R) :
    |(E w).re| ≤ (δ)*|w.re| ∧
      |(E w).im| ≤ (δ)*|w.im| := by
  let S := Metric.closedBall (0:ℂ) ‖w‖
  have hs (v : ℂ) (hv : v ∈ S) : ‖v‖^2 ≤ R := by
    have hn : ‖v‖ ≤ ‖w‖ := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hv
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hw
  have hd : ∀ v ∈ S, DifferentiableAt ℂ E v := fun v hv => hdiff v (hs v hv)
  have hb : ∀ v ∈ S, ‖deriv E v‖ ≤ δ := fun v hv => hderiv v (hs v hv)
  have hc : Convex ℝ S := convex_closedBall (0:ℂ) ‖w‖
  have hwm : w ∈ S := by simp [S]
  have hxr : (w.re:ℂ) ∈ S := by
    simpa only [S,Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs] using Complex.abs_re_le_norm w
  have hyi : Complex.I*(w.im:ℂ) ∈ S := by
    simpa only [S,Metric.mem_closedBall,dist_zero_right,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs] using Complex.abs_im_le_norm w
  constructor
  · have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hb hc hyi hwm
    have he : w-Complex.I*(w.im:ℂ) = (w.re:ℂ) := by apply Complex.ext <;> simp
    rw [he,Complex.norm_real,Real.norm_eq_abs] at hh
    have hp := Complex.abs_re_le_norm (E w-E (Complex.I*(w.im:ℂ)))
    rw [Complex.sub_re,(haxes w.im (by have hh := hw; rw [Complex.sq_norm,Complex.normSq_apply] at hh; nlinarith [sq_nonneg w.re])).2,sub_zero] at hp
    exact hp.trans hh
  · have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hb hc hxr hwm
    have he : w-(w.re:ℂ) = Complex.I*(w.im:ℂ) := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at hh
    have hp := Complex.abs_im_le_norm (E w-E (w.re:ℂ))
    rw [Complex.sub_im,(haxes w.re (by have hh := hw; rw [Complex.sq_norm,Complex.normSq_apply] at hh; nlinarith [sq_nonneg w.im])).1,sub_zero] at hp
    exact hp.trans hh

end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem inverse_error_coordinate_bounds (E : ℂ → ℂ) (γ δ : ℝ) (z : ℂ)
    (hx : 0 < z.re) (hy : 0 < z.im)
    (herr : |(E z⁻¹).re| ≤ δ*|(z⁻¹).re| ∧ |(E z⁻¹).im| ≤ δ*|(z⁻¹).im|) :
    let e := (γ:ℂ)*z⁻¹+E z⁻¹
    let U := z.re^2+z.im^2
    (γ-δ)/U ≤ e.re/z.re ∧ e.re/z.re ≤ (γ+δ)/U ∧
      -(γ+δ)/U ≤ e.im/z.im ∧ e.im/z.im ≤ -(γ-δ)/U := by
  let U := z.re^2+z.im^2
  have hUp : 0 < U := by dsimp [U]; nlinarith [sq_nonneg z.im]
  have hUn : Complex.normSq z = U := by simp [U,Complex.normSq_apply,pow_two]
  obtain ⟨hr,hi⟩ := herr
  have hwr : (z⁻¹).re = z.re/U := by rw [Complex.inv_re,hUn]
  have hwi : (z⁻¹).im = -z.im/U := by rw [Complex.inv_im,hUn]
  rw [hwr,abs_of_pos (div_pos hx hUp)] at hr
  rw [hwi,abs_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos hy) hUp)] at hi
  have hrlo := (abs_le.mp hr).1
  have hrhi := (abs_le.mp hr).2
  have hilo := (abs_le.mp hi).1
  have hihi := (abs_le.mp hi).2
  have hAr : ((γ:ℂ)*z⁻¹+E z⁻¹).re/z.re = γ/U+(E z⁻¹).re/z.re := by
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hwr]
    field_simp
  have hBi : ((γ:ℂ)*z⁻¹+E z⁻¹).im/z.im = -γ/U+(E z⁻¹).im/z.im := by
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,hwi]
    field_simp
  have herlo : -δ/U ≤ (E z⁻¹).re/z.re := by
    have hh := div_le_div_of_nonneg_right hrlo hx.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have herhi : (E z⁻¹).re/z.re ≤ δ/U := by
    have hh := div_le_div_of_nonneg_right hrhi hx.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have heilo : -δ/U ≤ (E z⁻¹).im/z.im := by
    have hh := div_le_div_of_nonneg_right hilo hy.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have heihi : (E z⁻¹).im/z.im ≤ δ/U := by
    have hh := div_le_div_of_nonneg_right hihi hy.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  dsimp only
  change (γ-δ)/U ≤ _ ∧ _ ≤ (γ+δ)/U ∧ -(γ+δ)/U ≤ _ ∧ _ ≤ -(γ-δ)/U
  rw [hAr,hBi]
  simp only [sub_div,add_div,neg_div] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩
end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem sixth_octic_radicand_real (x : ℝ) : sixthOcticRadicand (x:ℂ)=
    ((1-(2210/363)*x+(27455/2178)*x^2-(859775/84942)*x^3+
      (2088025/1019304)*x^4+(35496425/33637032)*x^5:ℝ):ℂ) := by
  simp [sixthOcticRadicand]
theorem sixth_octic_poly_real (x : ℝ) : sixthOcticPoly (x:ℂ)=
    ((1+x*(∑ i : Fin 20,sixthOcticCoeffs i*x^i.val):ℝ):ℂ) := by simp [sixthOcticPoly]
theorem sixth_octic_residual_real (x : ℝ) : sixthOcticResidual (x:ℂ)=
    ((∑ i : Fin 20,sixthOcticResidualCoeffs i*x^i.val:ℝ):ℂ) := by simp [sixthOcticResidual]
theorem sixth_octic_sqrt_real (x : ℝ) (hx : |x|≤3/10) :
    Complex.sqrt (sixthOcticRadicand (x:ℂ))=
      ((Real.sqrt (1-(2210/363)*x+(27455/2178)*x^2-(859775/84942)*x^3+
        (2088025/1019304)*x^4+(35496425/33637032)*x^5):ℝ):ℂ) := by
  have hp:=sixth_octic_real_positive x hx
  rw [sixth_octic_radicand_real,Complex.sqrt_of_nonneg (by exact_mod_cast hp.le),Complex.ofReal_re]

theorem sixth_octic_tail_real_axis (x : ℝ) (hx : x^2≤1/4) : (sixthOcticTail (x:ℂ)).im=0 := by
  unfold sixthOcticTail
  rw [show (x:ℂ)^2=((x^2:ℝ):ℂ) by norm_cast]
  rw [sixth_octic_sqrt_real _ (by rw [abs_of_nonneg (sq_nonneg x)]; linarith),sixth_octic_poly_real,sixth_octic_residual_real]
  rw [show (x:ℂ)^39=((x^39:ℝ):ℂ) by norm_cast]
  rw [show (17/33:ℂ)=((17/33:ℝ):ℂ) by norm_num]
  simp only [←Complex.ofReal_one,←Complex.ofReal_mul,←Complex.ofReal_sub,
    ←Complex.ofReal_add,←Complex.ofReal_neg,←Complex.ofReal_div,←Complex.ofReal_pow,Complex.ofReal_im]



theorem sixth_octic_error_axes (x : ℝ) (hx : x^2≤1/4) :
    (sixthOcticError (x:ℂ)).im=0 ∧ (sixthOcticError (Complex.I*(x:ℂ))).re=0 := by
  constructor
  · rw [sixthOcticError,Complex.add_im,sixth_octic_tail_real_axis x hx,add_zero]
    norm_num [sixthOcticPolynomialError,Fin.sum_univ_succ,←Complex.ofReal_pow,Complex.mul_im,Complex.mul_re]
  · rw [sixthOcticError,Complex.add_re,sixth_octic_tail_imaginary_axis x hx,add_zero]
    norm_num [sixthOcticPolynomialError,Fin.sum_univ_succ,mul_pow,Complex.I_pow_eq_pow_mod,
      ←Complex.ofReal_pow,Complex.mul_im,Complex.mul_re] <;> norm_num [Complex.I_pow_three]
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators






theorem sixth_octic_polynomial_error_hasDerivAt (w : ℂ) :
    HasDerivAt sixthOcticPolynomialError
      (∑ i : Fin 18,(sixthOcticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)) w := by
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [show 2*i.val+3-1=2*i.val+2 by omega,mul_assoc] using
    (hasDerivAt_pow (2*i.val+3) w).const_mul (sixthOcticErrorCoeffs i:ℂ)

theorem sixth_octic_polynomial_error_deriv_bound (w : ℂ) (hw : ‖w‖^2≤1/4) :
    ‖deriv sixthOcticPolynomialError w‖≤61/2000 := by
  rw [(sixth_octic_polynomial_error_hasDerivAt w).deriv]
  have hs : ‖∑ i : Fin 18,(sixthOcticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)‖≤
      ∑ i : Fin 18,|sixthOcticErrorCoeffs i| *((2*i.val+3:ℕ):ℝ)*(1/4:ℝ)^(i.val+1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    rw [show 2*i.val+2=2*(i.val+1) by omega,pow_mul]
    gcongr
  calc
    _≤_ := hs
    _≤∑ i : Fin 18,sixthOcticExpansionBounds i.succ*((2*i.val+3:ℕ):ℝ)*(1/4:ℝ)^(i.val+1) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact sixth_octic_coefficient_bounds.2.2.2 i.succ
    _≤61/2000 := by norm_num [sixthOcticExpansionBounds,Fin.sum_univ_succ]

theorem sixth_octic_error_differentiableAt (w : ℂ) (hw : ‖w‖^2≤1/4) :
    DifferentiableAt ℂ sixthOcticError w := by
  have hn : ‖w‖≤27/50 := by nlinarith [norm_nonneg w]
  exact (sixth_octic_polynomial_error_hasDerivAt w).differentiableAt.add (sixth_octic_tail_differentiableAt w hn)

theorem sixth_octic_error_deriv_bound (w : ℂ) (hw : ‖w‖^2≤1/4) :
    ‖deriv sixthOcticError w‖≤31/1000 := by
  have hn : ‖w‖≤27/50 := by nlinarith [norm_nonneg w]
  have hp:=sixth_octic_polynomial_error_deriv_bound w hw
  have ht:=sixth_octic_tail_deriv_bound w hw
  have hd : deriv sixthOcticError w=deriv sixthOcticPolynomialError w+deriv sixthOcticTail w := by
    exact deriv_add (sixth_octic_polynomial_error_hasDerivAt w).differentiableAt (sixth_octic_tail_differentiableAt w hn)
  rw [hd]
  have hs:=norm_add_le (deriv sixthOcticPolynomialError w) (deriv sixthOcticTail w)
  linarith
end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sixth_octic_leading_bounds : (38/1000:ℝ)<sixthOcticLeadingError ∧ sixthOcticLeadingError<39/1000 :=
  ⟨sixth_octic_coefficient_bounds.1,sixth_octic_coefficient_bounds.2.1⟩

theorem sixth_octic_error_coordinates (w : ℂ) (hw : ‖w‖^2≤1/4) :
    |(sixthOcticError w).re|≤(31/1000)*|w.re| ∧ |(sixthOcticError w).im|≤(31/1000)*|w.im| :=
  analytic_error_coordinate_bounds sixthOcticError (1/4) (31/1000)
    sixth_octic_error_differentiableAt sixth_octic_error_deriv_bound sixth_octic_error_axes w hw


end DerivativeChainPrivate

theorem solution (z : ℂ) (hx : 0<z.re) (hy : 0<z.im) (hX : 4≤z.re^2) :
    let U:=z.re^2+z.im^2
    0<(sixthOcticRemainder z).re/z.re ∧ (sixthOcticRemainder z).re/z.re≤(7/100)/U ∧
      -(7/100)/U≤(sixthOcticRemainder z).im/z.im ∧ (sixthOcticRemainder z).im/z.im<0 := by
  have hU : 4≤z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0<z.re^2+z.im^2 := by linarith
  have hn : ‖z⁻¹‖^2≤1/4 := by
    rw [norm_inv,inv_pow,Complex.sq_norm,Complex.normSq_apply]
    apply (inv_le_comm₀ (by nlinarith) (by norm_num)).mpr
    norm_num
    nlinarith
  obtain ⟨hAlo,hAhi,hBlo,hBhi⟩:=inverse_error_coordinate_bounds sixthOcticError sixthOcticLeadingError
    (31/1000) z hx hy (sixth_octic_error_coordinates z⁻¹ hn)
  obtain ⟨hgl,hgu⟩:=sixth_octic_leading_bounds
  have hp : 0<(sixthOcticLeadingError-31/1000)/(z.re^2+z.im^2) := div_pos (by linarith) hUp
  have hu : (sixthOcticLeadingError+31/1000)/(z.re^2+z.im^2)≤(7/100)/(z.re^2+z.im^2) :=
    div_le_div_of_nonneg_right (by linarith) hUp.le
  change 0<_ ∧ _≤_ ∧ _≤_ ∧ _< _
  change (sixthOcticLeadingError-31/1000)/_≤(sixthOcticRemainder z).re/z.re at hAlo
  change (sixthOcticRemainder z).re/z.re≤_ at hAhi
  change _≤(sixthOcticRemainder z).im/z.im at hBlo
  change (sixthOcticRemainder z).im/z.im≤_ at hBhi
  simp only [neg_div] at hBlo hBhi ⊢
  exact ⟨lt_of_lt_of_le hp hAlo,hAhi.trans hu,by linarith,by linarith⟩
