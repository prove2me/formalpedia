-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_septic_sharp_C_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:42:19.443816+00:00
-- url     : https://prove2.me/submissions/ce62fcdd-ba8b-46f3-ab7e-00815298c302

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthSepticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_SixthSepticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_inverse_odd_sum_bounds
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_radicand_positive
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




end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sixth_septic_leading_bounds :
    (9/200:ℝ)<sixthSepticLeadingError ∧ sixthSepticLeadingError<23/500 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤15145)
  have hp:=Real.sqrt_nonneg 15145
  dsimp only [sixthSepticLeadingError]
  constructor <;> nlinarith






end DerivativeChainPrivate

theorem solution (z : ℂ) (hx : 0<z.re) (hy : 0<z.im) (hX : 4≤z.re^2) :
    (3*((sixthSepticRemainder z).re/z.re)-(sixthSepticRemainder z).im/z.im)/2≤3/100 := by
  let k:=3*Real.sqrt 15145/2720
  let c : Fin 19 → ℝ:=Fin.cons sixthSepticLeadingError (fun i : Fin 18 => -k*sixthSepticErrorCoeffs i)
  let b : Fin 19 → ℝ:=Fin.cons (23/500) (fun i : Fin 18 => (17/125)*|sixthSepticErrorCoeffs i|)
  let E:=∑ i : Fin 19,(c i:ℂ)*(z⁻¹)^(2*i.val+1)
  let C:=fun e : ℂ => (3*(e.re/z.re)-e.im/z.im)/2
  have hk : 0<k := by dsimp [k]; positivity
  have hku : k≤17/125 := by
    have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤15145)
    have hp:=Real.sqrt_nonneg 15145
    dsimp [k]
    nlinarith
  have hg : 0<sixthSepticLeadingError := by linarith [sixth_septic_leading_bounds.1]
  have hc : ∀ i,|c i| ≤ b i := by
    intro i
    induction i using Fin.cases with
    | zero => simpa [c,b,abs_of_pos hg] using sixth_septic_leading_bounds.2.le
    | succ i =>
      simp only [c,b,Fin.cons_succ,abs_mul,abs_neg,abs_of_pos hk]
      exact mul_le_mul_of_nonneg_right hku (abs_nonneg _)
  have hFin:=(inverse_odd_sum_bounds c (fun i : Fin 19 => i.val) 4 (by norm_num) z hx hy hX).2
  have hNum : (∑ i : Fin 19,|c i| *(i.val+2:ℝ)*((4:ℝ)⁻¹)^(i.val+1))≤119/4000 := by
    calc
      _≤∑ i : Fin 19,b i*(i.val+2:ℝ)*((4:ℝ)⁻¹)^(i.val+1) := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        exact hc i
      _≤119/4000 := by norm_num [b,sixthSepticErrorCoeffs,Fin.sum_univ_succ]
  have hCF : C E≤119/4000 := (le_abs_self _).trans (hFin.trans hNum)
  have hInv : ‖z⁻¹‖^2≤1/4 := by
    rw [norm_inv,inv_pow,Complex.sq_norm,Complex.normSq_apply]
    apply (inv_le_comm₀ (by positivity) (by norm_num)).mpr
    norm_num
    nlinarith [sq_nonneg z.im]
  have hTail:=analytic_error_coordinate_bounds sixthSepticTail (1/4) (1/2000)
    (fun v hv => sixth_septic_tail_differentiableAt v (by nlinarith [norm_nonneg v]))
    (fun v hv => sixth_septic_tail_deriv_bound v (by linarith))
    (fun x hx => ⟨sixth_septic_tail_real_axis x (by linarith),sixth_septic_tail_imaginary_axis x (by linarith)⟩) z⁻¹ hInv
  obtain ⟨_,hA,hB,_⟩:=inverse_error_coordinate_bounds sixthSepticTail 0 (1/2000) z hx hy hTail
  simp only [Complex.ofReal_zero,zero_mul,zero_add] at hA hB
  have hU : 4≤z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0<z.re^2+z.im^2 := by linarith
  have hb : (1/2000:ℝ)/(z.re^2+z.im^2)≤1/8000 := by apply (div_le_iff₀ hUp).mpr; linarith
  rw [neg_div] at hB
  have hCT : C (sixthSepticTail z⁻¹)≤1/4000 := by dsimp [C]; linarith
  have he : sixthSepticRemainder z=E+sixthSepticTail z⁻¹ := by
    dsimp [E,c,sixthSepticRemainder,sixthSepticError,sixthSepticPolynomialError,k]
    simp [Fin.sum_univ_succ,Finset.mul_sum]
    push_cast
    ring
  change C (sixthSepticRemainder z)≤3/100
  rw [he]
  have hCadd : C (E+sixthSepticTail z⁻¹)=C E+C (sixthSepticTail z⁻¹) := by
    simp only [C,Complex.add_re,Complex.add_im,add_div]
    ring
  rw [hCadd]
  linarith
