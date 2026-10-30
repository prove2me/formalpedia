-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_weighted_corrections
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:45:31.733589+00:00
-- url     : https://prove2.me/submissions/e980050e-73ed-4b0e-8b84-10f69a961955

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthOcticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_inverse_odd_sum_bounds
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




end DerivativeChainPrivate

theorem solution (T : ℝ) (hT : 4≤T) (z : ℂ)
    (hx : 0<z.re) (hy : 0<z.im) (hX : T≤z.re^2) :
    (sixthOcticRemainder z).re/z.re≤
      (∑ i : Fin 19,sixthOcticExpansionBounds i*(T⁻¹)^(i.val+1))+(1/2000)/T ∧
    (3*((sixthOcticRemainder z).re/z.re)-(sixthOcticRemainder z).im/z.im)/2≤
      (∑ i : Fin 19,sixthOcticExpansionBounds i*(i.val+2:ℝ)*(T⁻¹)^(i.val+1))+2*((1/2000)/T) := by
  let E:=∑ i : Fin 19,(sixthOcticExpansionCoeffs i:ℂ)*(z⁻¹)^(2*i.val+1)
  let C:=fun e : ℂ => (3*(e.re/z.re)-e.im/z.im)/2
  have hTpos : 0<T := by linarith
  obtain ⟨hFiniteA,hFiniteC⟩:=inverse_odd_sum_bounds sixthOcticExpansionCoeffs
    (fun i : Fin 19 => i.val) T hTpos z hx hy hX
  have hNumA : (∑ i : Fin 19,|sixthOcticExpansionCoeffs i| *(T⁻¹)^(i.val+1))≤
      ∑ i : Fin 19,sixthOcticExpansionBounds i*(T⁻¹)^(i.val+1) := by
    apply Finset.sum_le_sum
    intro i _
    gcongr
    exact sixth_octic_coefficient_bounds.2.2.2 i
  have hNumC : (∑ i : Fin 19,|sixthOcticExpansionCoeffs i| *(i.val+2:ℝ)*(T⁻¹)^(i.val+1))≤
      ∑ i : Fin 19,sixthOcticExpansionBounds i*(i.val+2:ℝ)*(T⁻¹)^(i.val+1) := by
    apply Finset.sum_le_sum
    intro i _
    gcongr
    exact sixth_octic_coefficient_bounds.2.2.2 i
  have hFA : E.re/z.re≤∑ i : Fin 19,sixthOcticExpansionBounds i*(T⁻¹)^(i.val+1) :=
    (le_abs_self _).trans (hFiniteA.trans hNumA)
  have hFC : C E≤∑ i : Fin 19,sixthOcticExpansionBounds i*(i.val+2:ℝ)*(T⁻¹)^(i.val+1) :=
    (le_abs_self _).trans (hFiniteC.trans hNumC)
  have hU : T≤z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0<z.re^2+z.im^2 := by linarith
  have hInv : ‖z⁻¹‖^2≤1/4 := by
    rw [norm_inv,inv_pow,Complex.sq_norm,Complex.normSq_apply]
    apply (inv_le_comm₀ (by positivity) (by norm_num)).mpr
    norm_num
    nlinarith [sq_nonneg z.im]
  have hTail:=analytic_error_coordinate_bounds sixthOcticTail (1/4) (1/2000)
    (fun v hv => sixth_octic_tail_differentiableAt v (by nlinarith [norm_nonneg v]))
    sixth_octic_tail_deriv_bound
    (fun x hx => ⟨sixth_octic_tail_real_axis x hx,sixth_octic_tail_imaginary_axis x hx⟩) z⁻¹ hInv
  obtain ⟨_,hA,hB,_⟩:=inverse_error_coordinate_bounds sixthOcticTail 0 (1/2000) z hx hy hTail
  simp only [Complex.ofReal_zero,zero_mul,zero_add] at hA hB
  rw [neg_div] at hB
  have hb : (1/2000:ℝ)/(z.re^2+z.im^2)≤(1/2000)/T :=
    div_le_div_of_nonneg_left (by norm_num) hTpos hU
  have hTA : (sixthOcticTail z⁻¹).re/z.re≤(1/2000)/T := hA.trans hb
  have hTC : C (sixthOcticTail z⁻¹)≤2*((1/2000)/T) := by dsimp [C]; linarith
  have he : sixthOcticRemainder z=E+sixthOcticTail z⁻¹ := by
    dsimp [E,sixthOcticRemainder,sixthOcticError,sixthOcticPolynomialError,sixthOcticLeadingError]
    simp [sixthOcticErrorCoeffs,Fin.sum_univ_succ]
    ring
  constructor
  · rw [he,Complex.add_re,add_div]
    exact add_le_add hFA hTA
  · change C (sixthOcticRemainder z)≤_
    rw [he]
    have hCadd : C (E+sixthOcticTail z⁻¹)=C E+C (sixthOcticTail z⁻¹) := by
      simp only [C,Complex.add_re,Complex.add_im,add_div]
      ring
    rw [hCadd]
    exact add_le_add hFC hTC
