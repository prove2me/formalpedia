-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_septic_selected_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:03:18.069355+00:00
-- url     : https://prove2.me/submissions/a04819c5-be48-4492-942b-3c069d3ce034

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthSepticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_SixthSepticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_cubic_graph_coordinate_parts
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_radicand_positive
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_remainder_bounds
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_tail_deriv_bound
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_tail_differentiableAt
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_tail_imaginary_axis
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

theorem sixth_septic_radicand_real (x : ℝ) : sixthSepticRadicand (x:ℂ) =
    ((1-(2618/699)*x+(2890/699)*x^2-(122825/81783)*x^3+(417605/981396)*x^4:ℝ):ℂ) := by
  simp [sixthSepticRadicand]
theorem sixth_septic_poly_real (x : ℝ) : sixthSepticPoly (x:ℂ) =
    ((1+x*(∑ i : Fin 20, sixthSepticCoeffs i*x^i.val):ℝ):ℂ) := by
  simp [sixthSepticPoly]
theorem sixth_septic_residual_real (x : ℝ) : sixthSepticResidual (x:ℂ) =
    ((∑ i : Fin 20, sixthSepticResidualCoeffs i*x^i.val : ℝ):ℂ) := by
  simp [sixthSepticResidual]
theorem sixth_septic_sqrt_real (x : ℝ) (hx : |x| ≤ 3/8) : Complex.sqrt (sixthSepticRadicand (x:ℂ)) =
    ((Real.sqrt (1-(2618/699)*x+(2890/699)*x^2-(122825/81783)*x^3+(417605/981396)*x^4):ℝ):ℂ) := by
  have hp := sixth_septic_radicand_positive (x:ℂ) (by simpa using hx)
  rw [sixth_septic_radicand_real,Complex.ofReal_re] at hp
  rw [sixth_septic_radicand_real,Complex.sqrt_of_nonneg (by exact_mod_cast hp.le),Complex.ofReal_re]

theorem sixth_septic_tail_real_axis (x : ℝ) (hx : x^2 ≤ 2/7) : (sixthSepticTail (x:ℂ)).im = 0 := by
  unfold sixthSepticTail
  rw [show (x:ℂ)^2 = ((x^2:ℝ):ℂ) by norm_cast]
  rw [sixth_septic_sqrt_real _ (by rw [abs_of_nonneg (sq_nonneg x)]; linarith),sixth_septic_poly_real,sixth_septic_residual_real]
  rw [← Complex.ofReal_pow]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div,Complex.ofReal_im]



theorem sixth_septic_error_axes (x : ℝ) (hx : x^2 ≤ 2/7) :
    (sixthSepticError (x:ℂ)).im = 0 ∧ (sixthSepticError (Complex.I*(x:ℂ))).re = 0 := by
  constructor
  · rw [sixthSepticError,Complex.add_im,sixth_septic_tail_real_axis x hx,add_zero]
    norm_num [sixthSepticPolynomialError,Fin.sum_univ_succ,← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re]
  · rw [sixthSepticError,Complex.add_re,sixth_septic_tail_imaginary_axis x hx,add_zero]
    norm_num [sixthSepticPolynomialError,Fin.sum_univ_succ,mul_pow,Complex.I_pow_eq_pow_mod,
      ← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re] <;> norm_num [Complex.I_pow_three]
end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators




theorem sixth_septic_polynomial_error_hasDerivAt (w : ℂ) :
    HasDerivAt sixthSepticPolynomialError
      (-((3*Real.sqrt 15145/2720:ℝ):ℂ)*(∑ i : Fin 18,
        (sixthSepticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2))) w := by
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [show 2*i.val+3-1=2*i.val+2 by omega,mul_assoc] using
    (hasDerivAt_pow (2*i.val+3) w).const_mul (sixthSepticErrorCoeffs i:ℂ)



theorem sixth_septic_polynomial_error_deriv_bound_refined (w : ℂ) (hw : ‖w‖^2≤1/4) :
    ‖deriv sixthSepticPolynomialError w‖≤63/2000 := by
  have hk : 0<(3*Real.sqrt 15145/2720:ℝ) := by positivity
  have hku : (3*Real.sqrt 15145/2720:ℝ)≤7/50 := by
    have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤15145)
    have hp:=Real.sqrt_nonneg 15145
    nlinarith
  rw [(sixth_septic_polynomial_error_hasDerivAt w).deriv]
  rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
  have hsum : ‖∑ i : Fin 18,(sixthSepticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)‖≤
      ∑ i : Fin 18,|sixthSepticErrorCoeffs i| *((2*i.val+3:ℕ):ℝ)*(1/4:ℝ)^(i.val+1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    rw [show 2*i.val+2=2*(i.val+1) by omega,pow_mul]
    gcongr
  calc
    _≤(7/50:ℝ)*(∑ i : Fin 18,|sixthSepticErrorCoeffs i| *((2*i.val+3:ℕ):ℝ)*(1/4:ℝ)^(i.val+1)) :=
      mul_le_mul hku hsum (norm_nonneg _) (by norm_num)
    _≤63/2000 := by norm_num [sixthSepticErrorCoeffs,Fin.sum_univ_succ]

theorem sixth_septic_error_differentiableAt (w : ℂ) (hw : ‖w‖^2≤2/7) :
    DifferentiableAt ℂ sixthSepticError w := by
  have hn : ‖w‖≤3/5 := by nlinarith [norm_nonneg w]
  exact (sixth_septic_polynomial_error_hasDerivAt w).differentiableAt.add (sixth_septic_tail_differentiableAt w hn)



theorem sixth_septic_error_deriv_bound_refined (w : ℂ) (hw : ‖w‖^2≤1/4) :
    ‖deriv sixthSepticError w‖≤4/125 := by
  have hw2 : ‖w‖^2≤2/7 := by linarith
  have hn : ‖w‖≤3/5 := by nlinarith [norm_nonneg w]
  have hp:=sixth_septic_polynomial_error_deriv_bound_refined w hw
  have ht:=sixth_septic_tail_deriv_bound w hw2
  have hd : deriv sixthSepticError w=deriv sixthSepticPolynomialError w+deriv sixthSepticTail w := by
    exact deriv_add (sixth_septic_polynomial_error_hasDerivAt w).differentiableAt (sixth_septic_tail_differentiableAt w hn)
  rw [hd]
  have hh:=norm_add_le (deriv sixthSepticPolynomialError w) (deriv sixthSepticTail w)
  linarith
end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sixth_septic_leading_bounds :
    (9/200:ℝ)<sixthSepticLeadingError ∧ sixthSepticLeadingError<23/500 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤15145)
  have hp:=Real.sqrt_nonneg 15145
  dsimp only [sixthSepticLeadingError]
  constructor <;> nlinarith



theorem sixth_septic_error_coordinates_refined (w : ℂ) (hw : ‖w‖^2≤1/4) :
    |(sixthSepticError w).re|≤(4/125)*|w.re| ∧ |(sixthSepticError w).im|≤(4/125)*|w.im| :=
  analytic_error_coordinate_bounds sixthSepticError (1/4) (4/125)
    (fun v hv => sixth_septic_error_differentiableAt v (by linarith))
    sixth_septic_error_deriv_bound_refined (fun x hx => sixth_septic_error_axes x (by linarith)) w hw


end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sixth_septic_scalar_gaps :
    (3/100:ℝ)<(455-3*Real.sqrt 15145)/2720 ∧
    (455-3*Real.sqrt 15145)/2720<4/125 ∧
    (1/20:ℝ)<(455-3*Real.sqrt 19565)/680 ∧
    (455-3*Real.sqrt 19565)/680<3/50 ∧
    (455-3*Real.sqrt 15145)/2720<(455-3*Real.sqrt 19565)/680 ∧
    (1/20:ℝ)<(559-3*Real.sqrt 19565)/688-(13/32-77*Real.sqrt 15145/37280) ∧
    (29/1600:ℝ)<(559-3*Real.sqrt 19565)/688-(7/2)*((455-3*Real.sqrt 19565)/680) ∧
    (1/40:ℝ)<(13/32-77*Real.sqrt 15145/37280)-4*((455-3*Real.sqrt 15145)/2720) ∧
    (3/10:ℝ)<(455+3*Real.sqrt 15145)/2720 ∧
    13/32+77*Real.sqrt 15145/37280<2/3 ∧
    (1/5:ℝ)<(559-3*Real.sqrt 19565)/688 := by
  have h1:=Real.sq_sqrt (by norm_num : (0:ℝ)≤15145)
  have p1:=Real.sqrt_nonneg 15145
  have h2:=Real.sq_sqrt (by norm_num : (0:ℝ)≤19565)
  have p2:=Real.sqrt_nonneg 19565
  have l1 : (1230650:ℝ)/10000<Real.sqrt 15145 := by nlinarith only [h1,p1]
  have u1 : Real.sqrt 15145<(1230651:ℝ)/10000 := by nlinarith only [h1,p1]
  have l2 : (1398749:ℝ)/10000<Real.sqrt 19565 := by nlinarith only [h2,p2]
  have u2 : Real.sqrt 19565<(1398750:ℝ)/10000 := by nlinarith only [h2,p2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [l1,u1,l2,u2]
end DerivativeChainPrivate

theorem solution (β z : ℂ) (hR : 0≤β.re) (hx : 0<z.re) (hy : 0<z.im)
    (hX : 7/2≤z.re^2)
    (hg : β/z=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
      ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder z/z) :
    4<z.re^2 ∧ (sixthSepticRemainder z).re/z.re≤39/2000 ∧
      (sixthSepticRemainder z).im/z.im≤0 ∧
      (3*((sixthSepticRemainder z).re/z.re)-(sixthSepticRemainder z).im/z.im)/2≤39/1000 ∧
      4≤z.re^2-3*z.im^2 := by
  let α:=(455-3*Real.sqrt 15145)/2720
  let b:=13/32-77*Real.sqrt 15145/37280
  obtain ⟨hα,_,_,_,_,_,_,hslack,_,_,_⟩:=sixth_septic_scalar_gaps
  change (3/100:ℝ)<α at hα
  change (1/40:ℝ)<b-4*α at hslack
  have hz : z≠0 := by intro he; simp [he] at hx
  have hr:=(cubic_graph_coordinate_parts β z (sixthSepticRemainder z) α b hz hg).1
  have hRp : β.re/z.re=α*(z.re^2-3*z.im^2)-b+(sixthSepticRemainder z).re/z.re := by rw [hr]; field_simp
  have hnonneg : 0≤β.re/z.re := div_nonneg hR hx.le
  obtain ⟨hAp,hAr,hBr,hBn⟩:=sixth_septic_remainder_bounds z hx hy hX
  have hU : 7/2≤z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0<z.re^2+z.im^2 := by linarith
  have hAu0 : (sixthSepticRemainder z).re/z.re≤1/40 := by
    apply hAr.trans
    apply (div_le_iff₀ hUp).mpr
    linarith
  have hterm:=mul_nonneg (show 0≤α by linarith) (sq_nonneg z.im)
  have hX1 : 4<z.re^2 := by
    have ht : α*4<α*z.re^2 := by nlinarith only [hRp,hnonneg,hAu0,hslack,hterm]
    exact lt_of_mul_lt_mul_left ht (by linarith only [hα])
  have hn : ‖z⁻¹‖^2≤1/4 := by
    rw [norm_inv,inv_pow,Complex.sq_norm,Complex.normSq_apply]
    apply (inv_le_comm₀ (by nlinarith) (by norm_num)).mpr
    norm_num
    nlinarith [sq_nonneg z.im]
  obtain ⟨_,hA,hB,_⟩:=inverse_error_coordinate_bounds sixthSepticError sixthSepticLeadingError
    (4/125) z hx hy (sixth_septic_error_coordinates_refined z⁻¹ hn)
  change (sixthSepticRemainder z).re/z.re≤_ at hA
  change _≤(sixthSepticRemainder z).im/z.im at hB
  have hu : (sixthSepticLeadingError+4/125)/(z.re^2+z.im^2)≤39/2000 := by
    apply (div_le_iff₀ hUp).mpr
    have hgu:=sixth_septic_leading_bounds.2
    nlinarith only [hX1,hgu,sq_nonneg z.im]
  have hAu : (sixthSepticRemainder z).re/z.re≤39/2000 := hA.trans hu
  simp only [neg_div] at hB
  have hBl : -(39/2000)≤(sixthSepticRemainder z).im/z.im := by linarith only [hB,hu]
  refine ⟨hX1,hAu,hBn.le,by linarith,?_⟩
  have ht : α*4<α*(z.re^2-3*z.im^2) := by linarith only [hRp,hnonneg,hAu,hslack]
  exact (lt_of_mul_lt_mul_left ht (by linarith only [hα])).le
