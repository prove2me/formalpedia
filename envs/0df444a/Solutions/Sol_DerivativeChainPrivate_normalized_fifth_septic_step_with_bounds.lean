-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fifth_septic_step_with_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T23:10:09.58626+00:00
-- url     : https://prove2.me/submissions/41da21f3-01b8-4333-800b-67b5027c09b9

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_septic_step
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


section
-- Source module: VerifiedCube

open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate













end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cubic_graph_coordinate_parts (β z e : ℂ) (α b : ℝ) (hz : z ≠ 0)
    (hβ : β/z = (α : ℂ)*z^2-(b : ℂ)+e/z) :
    β.re = z.re * (α*(z.re^2-3*z.im^2)-b)+e.re ∧
      β.im = z.im * (α*(3*z.re^2-z.im^2)-b)+e.im ∧
      (β/z).im = 2*α*z.re*z.im+(e/z).im := by
  have hgraph : β = (α : ℂ)*z^3-(b : ℂ)*z+e := by
    calc
      _ = ((α : ℂ)*z^2-(b : ℂ)+e/z)*z := (div_eq_iff hz).mp hβ
      _ = _ := by rw [add_mul,sub_mul,div_mul_cancel₀ _ hz]; ring
  refine ⟨?_,?_,?_⟩
  · rw [hgraph]
    simp only [pow_succ,pow_zero,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im]
    ring
  · rw [hgraph]
    simp only [pow_succ,pow_zero,Complex.add_im,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im]
    ring
  · rw [hβ]
    simp only [pow_two,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im]
    ring



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



end


section
-- Source module: SepticSqrtAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators















theorem norm_real_power_sum_le {n : ℕ} (c : Fin n → ℝ) (u : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hu : ‖u‖ ≤ R) :
    ‖∑ i : Fin n, (c i:ℂ)*u^i.val‖ ≤ ∑ i : Fin n, |c i| *R^i.val := by
  calc
    _ ≤ ∑ i : Fin n, ‖(c i:ℂ)*u^i.val‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      gcongr











end DerivativeChainPrivate

end


section
-- Source module: FifthSepticAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators








theorem fifth_septic_poly_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    ‖fifthSepticPoly u-1‖ ≤ 3/4 := by
  have hs := norm_real_power_sum_le fifthSepticCoeffs u (9/4) (by norm_num) hu
  calc
    _ = ‖u‖*‖∑ i : Fin 24, (fifthSepticCoeffs i:ℂ)*u^i.val‖ := by simp [fifthSepticPoly,norm_mul]
    _ ≤ (9/4)*(∑ i : Fin 24, |fifthSepticCoeffs i| *(9/4:ℝ)^i.val) :=
      mul_le_mul hu hs (norm_nonneg _) (by norm_num)
    _ ≤ 3/4 := by norm_num [fifthSepticCoeffs,Fin.sum_univ_succ]

theorem fifth_septic_residual_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    ‖fifthSepticResidual u‖ ≤ 1/10000000000000000 := by
  apply (norm_real_power_sum_le fifthSepticResidualCoeffs u (9/4) (by norm_num) hu).trans
  norm_num [fifthSepticResidualCoeffs,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticSlit

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DerivativeChainPrivate

theorem fifth_septic_radicand_positive (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    0 < (fifthSepticRadicand u).re := by
  let x := u.re
  let Y := u.im^2
  let V := (9/4:ℝ)^2-x^2
  have hx : |x| ≤ 9/4 := (Complex.abs_re_le_norm u).trans hu
  have hxlo : -(9/4:ℝ) ≤ x := (abs_le.mp hx).1
  have hxhi : x ≤ 9/4 := (abs_le.mp hx).2
  have hy : 0 ≤ Y := sq_nonneg _
  have hyV : Y ≤ V := by
    have hn := Complex.sq_norm u
    simp only [Complex.normSq_apply] at hn
    dsimp [Y,V,x]
    nlinarith [norm_nonneg u]
  let B := -(20/209:ℝ)+(96/5643)*x-(24/16929)*x^2
  have hB : B+(4/16929)*(Y+V) ≤ 0 := by
    dsimp [B,V] at *
    nlinarith [sq_nonneg x]
  have hd := mul_nonneg (sub_nonneg.mpr hyV) (neg_nonneg.mpr hB)
  have he : (fifthSepticRadicand u).re =
      1-(32/57)*x+(20/209)*x^2-(32/5643)*x^3+(4/16929)*x^4+B*Y+(4/16929)*Y^2 := by
    dsimp [fifthSepticRadicand,x,Y,B]
    norm_num [pow_succ,Complex.mul_re,Complex.mul_im]
    ring
  have hbase :
      0 < 1-(32/57)*x+(20/209)*x^2-(32/5643)*x^3+(4/16929)*x^4+B*V+(4/16929)*V^2 := by
    have hx3 := mul_nonneg (sub_nonneg.mpr hxhi) (sq_nonneg x)
    have hsq := sq_nonneg (x-149/82)
    have hx4 := sq_nonneg (x^2)
    dsimp [B,V]
    nlinarith
  rw [he]
  nlinarith

theorem fifth_septic_slit (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    fifthSepticRadicand u ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (fifth_septic_radicand_positive u hu))

theorem fifth_septic_denominator_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    Complex.sqrt (fifthSepticRadicand u)+fifthSepticPoly u ≠ 0 ∧
      ‖(Complex.sqrt (fifthSepticRadicand u)+fifthSepticPoly u)⁻¹‖ ≤ 4 := by
  have hs : 0 ≤ (Complex.sqrt (fifthSepticRadicand u)).re := by
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hp := fifth_septic_poly_bound u hu
  have hr := Complex.re_le_norm (1-fifthSepticPoly u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re,Complex.one_re] at hr
  have hd := Complex.re_le_norm (Complex.sqrt (fifthSepticRadicand u)+fifthSepticPoly u)
  simp only [Complex.add_re] at hd
  have hl : (1/4:ℝ) ≤ ‖Complex.sqrt (fifthSepticRadicand u)+fifthSepticPoly u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi := inv_anti₀ (by norm_num : (0:ℝ) < 1/4) hl
  norm_num at hi
  exact hi
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticTail

set_option autoImplicit false
namespace DerivativeChainPrivate



theorem fifth_septic_tail_norm (w : ℂ) (hw : ‖w‖ ≤ 3/2) : ‖fifthSepticTail w‖ ≤ 1/1000000 := by
  have hu : ‖w^2‖ ≤ 9/4 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hk : 0 < (3*Real.sqrt 209/4:ℝ) := by positivity
  have hku : (3*Real.sqrt 209/4:ℝ) ≤ 11 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
    have hp := Real.sqrt_nonneg 209
    nlinarith
  have ht := fifth_septic_residual_bound (w^2) hu
  have hd := (fifth_septic_denominator_bound (w^2) hu).2
  calc
    _ = (3*Real.sqrt 209/4:ℝ)*‖w‖^47*‖fifthSepticResidual (w^2)‖*
        ‖(Complex.sqrt (fifthSepticRadicand (w^2))+fifthSepticPoly (w^2))⁻¹‖ := by
      simp only [fifthSepticTail,div_eq_mul_inv,norm_mul,norm_neg,norm_pow,Complex.norm_real,
        Real.norm_eq_abs]
      norm_num [abs_of_nonneg (Real.sqrt_nonneg 209)]
    _ ≤ (11:ℝ)*(3/2)^47*(1/10000000000000000)*4 := by gcongr
    _ ≤ 1/1000000 := by norm_num

theorem fifth_septic_tail_differentiableAt (w : ℂ) (hw : ‖w‖ ≤ 3/2) :
    DifferentiableAt ℂ fifthSepticTail w := by
  have hu : ‖w^2‖ ≤ 9/4 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hh : DifferentiableAt ℂ (fun v : ℂ => fifthSepticRadicand (v^2)) w := by
    unfold fifthSepticRadicand
    fun_prop
  have hs : DifferentiableAt ℂ (fun v : ℂ => Complex.sqrt (fifthSepticRadicand (v^2))) w := by
    simpa only [Function.comp_def] using
      (Complex.differentiableAt_sqrt (fifth_septic_slit (w^2) hu)).comp w hh
  have hp : DifferentiableAt ℂ (fun v : ℂ => fifthSepticPoly (v^2)) w := by
    unfold fifthSepticPoly
    fun_prop
  have ht : DifferentiableAt ℂ (fun v : ℂ => fifthSepticResidual (v^2)) w := by
    unfold fifthSepticResidual
    fun_prop
  have hd := (fifth_septic_denominator_bound (w^2) hu).1
  unfold fifthSepticTail
  fun_prop

theorem fifth_septic_tail_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    ‖deriv fifthSepticTail w‖ ≤ 1/25000 := by
  have hw' : ‖w‖ ≤ 29/20 := by nlinarith [norm_nonneg w]
  have hball : ∀ u ∈ Metric.ball w (1/20:ℝ), ‖u‖ ≤ 3/2 := by
    intro u hu
    have hd : ‖u-w‖ < 1/20 := by simpa only [Metric.mem_ball,dist_eq_norm] using hu
    have hn := norm_le_norm_sub_add u w
    linarith
  have hd : DifferentiableOn ℂ fifthSepticTail (Metric.ball w (1/20:ℝ)) := by
    intro u hu
    exact (fifth_septic_tail_differentiableAt u (hball u hu)).differentiableWithinAt
  have hm : Set.MapsTo fifthSepticTail (Metric.ball w (1/20:ℝ))
      (Metric.closedBall (fifthSepticTail w) (1/500000:ℝ)) := by
    intro u hu
    rw [Metric.mem_closedBall,dist_eq_norm]
    have h1 := fifth_septic_tail_norm u (hball u hu)
    have h2 := fifth_septic_tail_norm w (by linarith)
    have hn := norm_sub_le (fifthSepticTail u) (fifthSepticTail w)
    linarith
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hd hm (by norm_num : (0:ℝ) < 1/20)
  norm_num at hh
  exact hh
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticErrorDerivative


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open scoped BigOperators







theorem fifth_septic_polynomial_error_hasDerivAt (w : ℂ) :
    HasDerivAt fifthSepticPolynomialError
      (-((3*Real.sqrt 209/4:ℝ):ℂ)*(∑ i : Fin 22,
        (fifthSepticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2))) w := by
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [show 2*i.val+3-1=2*i.val+2 by omega,mul_assoc] using
    (hasDerivAt_pow (2*i.val+3) w).const_mul (fifthSepticErrorCoeffs i:ℂ)

theorem fifth_septic_polynomial_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    ‖deriv fifthSepticPolynomialError w‖ ≤ 559/10000 := by
  have hk : 0 < (3*Real.sqrt 209/4:ℝ) := by positivity
  have hku : (3*Real.sqrt 209/4:ℝ) ≤ 10843/1000 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
    have hp := Real.sqrt_nonneg 209
    nlinarith
  rw [(fifth_septic_polynomial_error_hasDerivAt w).deriv]
  rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
  have hsum : ‖∑ i : Fin 22, (fifthSepticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)‖ ≤
      ∑ i : Fin 22, |fifthSepticErrorCoeffs i| * ((2*i.val+3:ℕ):ℝ)*(2:ℝ)^(i.val+1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    rw [show 2*i.val+2=2*(i.val+1) by omega,pow_mul]
    gcongr
  calc
    _ ≤ (10843/1000:ℝ)*(∑ i : Fin 22, |fifthSepticErrorCoeffs i| * ((2*i.val+3:ℕ):ℝ)*(2:ℝ)^(i.val+1)) :=
      mul_le_mul hku hsum (norm_nonneg _) (by norm_num)
    _ ≤ 559/10000 := by norm_num [fifthSepticErrorCoeffs,Fin.sum_univ_succ]

theorem fifth_septic_error_differentiableAt (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    DifferentiableAt ℂ fifthSepticError w := by
  have hn : ‖w‖ ≤ 3/2 := by nlinarith [norm_nonneg w]
  exact (fifth_septic_polynomial_error_hasDerivAt w).differentiableAt.add (fifth_septic_tail_differentiableAt w hn)

theorem fifth_septic_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    ‖deriv fifthSepticError w‖ ≤ 7/125 := by
  have hn : ‖w‖ ≤ 3/2 := by nlinarith [norm_nonneg w]
  have hp := fifth_septic_polynomial_error_deriv_bound w hw
  have ht := fifth_septic_tail_deriv_bound w hw
  have hd : deriv fifthSepticError w = deriv fifthSepticPolynomialError w+deriv fifthSepticTail w := by
    exact deriv_add (fifth_septic_polynomial_error_hasDerivAt w).differentiableAt (fifth_septic_tail_differentiableAt w hn)
  rw [hd]
  have hs := norm_add_le (deriv fifthSepticPolynomialError w) (deriv fifthSepticTail w)
  linarith

theorem fifth_septic_polynomial_error_deriv_bound_refined (w : ℂ) (hw : ‖w‖^2 ≤ 50/29) :
    ‖deriv fifthSepticPolynomialError w‖ ≤ 429/10000 := by
  have hk : 0 < (3*Real.sqrt 209/4:ℝ) := by positivity
  have hku : (3*Real.sqrt 209/4:ℝ) ≤ 10843/1000 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
    have hp := Real.sqrt_nonneg 209
    nlinarith
  rw [(fifth_septic_polynomial_error_hasDerivAt w).deriv]
  rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
  have hsum : ‖∑ i : Fin 22, (fifthSepticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)‖ ≤
      ∑ i : Fin 22, |fifthSepticErrorCoeffs i| * ((2*i.val+3:ℕ):ℝ)*(50/29:ℝ)^(i.val+1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    rw [show 2*i.val+2=2*(i.val+1) by omega,pow_mul]
    gcongr
  calc
    _ ≤ (10843/1000:ℝ)*(∑ i : Fin 22, |fifthSepticErrorCoeffs i| * ((2*i.val+3:ℕ):ℝ)*(50/29:ℝ)^(i.val+1)) :=
      mul_le_mul hku hsum (norm_nonneg _) (by norm_num)
    _ ≤ 429/10000 := by norm_num [fifthSepticErrorCoeffs,Fin.sum_univ_succ]


theorem fifth_septic_polynomial_error_deriv_bound_final (w : ℂ) (hw : ‖w‖^2 ≤ 5/3) :
    ‖deriv fifthSepticPolynomialError w‖ ≤ 399/10000 := by
  have hk : 0 < (3*Real.sqrt 209/4:ℝ) := by positivity
  have hku : (3*Real.sqrt 209/4:ℝ) ≤ 10843/1000 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
    have hp := Real.sqrt_nonneg 209
    nlinarith
  rw [(fifth_septic_polynomial_error_hasDerivAt w).deriv]
  rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
  have hsum : ‖∑ i : Fin 22, (fifthSepticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)‖ ≤
      ∑ i : Fin 22, |fifthSepticErrorCoeffs i| * ((2*i.val+3:ℕ):ℝ)*(5/3:ℝ)^(i.val+1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    rw [show 2*i.val+2=2*(i.val+1) by omega,pow_mul]
    gcongr
  calc
    _ ≤ (10843/1000:ℝ)*(∑ i : Fin 22, |fifthSepticErrorCoeffs i| * ((2*i.val+3:ℕ):ℝ)*(5/3:ℝ)^(i.val+1)) :=
      mul_le_mul hku hsum (norm_nonneg _) (by norm_num)
    _ ≤ 399/10000 := by norm_num [fifthSepticErrorCoeffs,Fin.sum_univ_succ]


theorem fifth_septic_error_deriv_bound_refined (w : ℂ) (hw : ‖w‖^2 ≤ 50/29) :
    ‖deriv fifthSepticError w‖ ≤ 43/1000 := by
  have hw2 : ‖w‖^2 ≤ 2 := by linarith
  have hn : ‖w‖ ≤ 3/2 := by nlinarith [norm_nonneg w]
  have hp := fifth_septic_polynomial_error_deriv_bound_refined w hw
  have ht := fifth_septic_tail_deriv_bound w hw2
  have hd : deriv fifthSepticError w = deriv fifthSepticPolynomialError w+deriv fifthSepticTail w := by
    exact deriv_add (fifth_septic_polynomial_error_hasDerivAt w).differentiableAt (fifth_septic_tail_differentiableAt w hn)
  rw [hd]
  have hs := norm_add_le (deriv fifthSepticPolynomialError w) (deriv fifthSepticTail w)
  linarith

theorem fifth_septic_error_deriv_bound_final (w : ℂ) (hw : ‖w‖^2 ≤ 5/3) :
    ‖deriv fifthSepticError w‖ ≤ 1/25 := by
  have hw2 : ‖w‖^2 ≤ 2 := by linarith
  have hn : ‖w‖ ≤ 3/2 := by nlinarith [norm_nonneg w]
  have hp := fifth_septic_polynomial_error_deriv_bound_final w hw
  have ht := fifth_septic_tail_deriv_bound w hw2
  have hd : deriv fifthSepticError w = deriv fifthSepticPolynomialError w+deriv fifthSepticTail w := by
    exact deriv_add (fifth_septic_polynomial_error_hasDerivAt w).differentiableAt (fifth_septic_tail_differentiableAt w hn)
  rw [hd]
  have hs := norm_add_le (deriv fifthSepticPolynomialError w) (deriv fifthSepticTail w)
  linarith

end DerivativeChainPrivate

end


section
-- Source module: FifthSepticAxes

set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem fifth_septic_radicand_real (x : ℝ) : fifthSepticRadicand (x:ℂ) =
    ((1-(32/57)*x+(20/209)*x^2-(32/5643)*x^3+(4/16929)*x^4:ℝ):ℂ) := by
  simp [fifthSepticRadicand]
theorem fifth_septic_poly_real (x : ℝ) : fifthSepticPoly (x:ℂ) =
    ((1+x*(∑ i : Fin 24, fifthSepticCoeffs i*x^i.val):ℝ):ℂ) := by
  simp [fifthSepticPoly]
theorem fifth_septic_residual_real (x : ℝ) : fifthSepticResidual (x:ℂ) =
    ((∑ i : Fin 24, fifthSepticResidualCoeffs i*x^i.val : ℝ):ℂ) := by
  simp [fifthSepticResidual]
theorem fifth_septic_sqrt_real (x : ℝ) (hx : |x| ≤ 9/4) : Complex.sqrt (fifthSepticRadicand (x:ℂ)) =
    ((Real.sqrt (1-(32/57)*x+(20/209)*x^2-(32/5643)*x^3+(4/16929)*x^4):ℝ):ℂ) := by
  have hp := fifth_septic_radicand_positive (x:ℂ) (by simpa using hx)
  rw [fifth_septic_radicand_real,Complex.ofReal_re] at hp
  rw [fifth_septic_radicand_real,Complex.sqrt_of_nonneg (by exact_mod_cast hp.le),Complex.ofReal_re]

theorem fifth_septic_tail_real_axis (x : ℝ) (hx : x^2 ≤ 2) : (fifthSepticTail (x:ℂ)).im = 0 := by
  unfold fifthSepticTail
  rw [show (x:ℂ)^2 = ((x^2:ℝ):ℂ) by norm_cast]
  rw [fifth_septic_sqrt_real _ (by rw [abs_of_nonneg (sq_nonneg x)]; linarith),fifth_septic_poly_real,fifth_septic_residual_real]
  rw [← Complex.ofReal_pow]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div,Complex.ofReal_im]

theorem fifth_septic_tail_imaginary_axis (x : ℝ) (hx : x^2 ≤ 2) : (fifthSepticTail (Complex.I*(x:ℂ))).re = 0 := by
  unfold fifthSepticTail
  rw [show (Complex.I*(x:ℂ))^2 = ((-x^2:ℝ):ℂ) by norm_num [mul_pow]]
  rw [fifth_septic_sqrt_real _ (by rw [abs_neg,abs_of_nonneg (sq_nonneg x)]; linarith),fifth_septic_poly_real,fifth_septic_residual_real]
  have he : (Complex.I*(x:ℂ))^47 = -Complex.I*((x^47:ℝ):ℂ) := by
    norm_num [mul_pow,Complex.I_pow_eq_pow_mod]
    norm_num [Complex.I_pow_three]
  rw [he]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div]
  simp only [Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,zero_add,add_zero,sub_zero,zero_sub,
    mul_one,one_mul,neg_zero,zero_div]

theorem fifth_septic_error_axes (x : ℝ) (hx : x^2 ≤ 2) :
    (fifthSepticError (x:ℂ)).im = 0 ∧ (fifthSepticError (Complex.I*(x:ℂ))).re = 0 := by
  constructor
  · rw [fifthSepticError,Complex.add_im,fifth_septic_tail_real_axis x hx,add_zero]
    norm_num [fifthSepticPolynomialError,Fin.sum_univ_succ,← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re]
  · rw [fifthSepticError,Complex.add_re,fifth_septic_tail_imaginary_axis x hx,add_zero]
    norm_num [fifthSepticPolynomialError,Fin.sum_univ_succ,mul_pow,Complex.I_pow_eq_pow_mod,
      ← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re] <;> norm_num [Complex.I_pow_three]
end DerivativeChainPrivate

end


section
-- Source module: AnalyticErrorCoordinates


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

end


section
-- Source module: InverseErrorCoordinates

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

end


section
-- Source module: FifthSepticCoordinates

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_septic_leading_bounds : (3/40:ℝ) < fifthSepticLeadingError ∧ fifthSepticLeadingError < 151/2000 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
  have hp := Real.sqrt_nonneg 209
  dsimp only [fifthSepticLeadingError]
  constructor <;> nlinarith

theorem fifth_septic_error_coordinates (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    |(fifthSepticError w).re| ≤ (7/125)*|w.re| ∧ |(fifthSepticError w).im| ≤ (7/125)*|w.im| :=
  analytic_error_coordinate_bounds fifthSepticError 2 (7/125)
    fifth_septic_error_differentiableAt fifth_septic_error_deriv_bound fifth_septic_error_axes w hw

theorem fifth_septic_error_coordinates_refined (w : ℂ) (hw : ‖w‖^2 ≤ 50/29) :
    |(fifthSepticError w).re| ≤ (43/1000)*|w.re| ∧ |(fifthSepticError w).im| ≤ (43/1000)*|w.im| :=
  analytic_error_coordinate_bounds fifthSepticError (50/29) (43/1000)
    (fun v hv => fifth_septic_error_differentiableAt v (by linarith))
    fifth_septic_error_deriv_bound_refined (fun x hx => fifth_septic_error_axes x (by linarith)) w hw

theorem fifth_septic_error_coordinates_final (w : ℂ) (hw : ‖w‖^2 ≤ 5/3) :
    |(fifthSepticError w).re| ≤ (1/25)*|w.re| ∧ |(fifthSepticError w).im| ≤ (1/25)*|w.im| :=
  analytic_error_coordinate_bounds fifthSepticError (5/3) (1/25)
    (fun v hv => fifth_septic_error_differentiableAt v (by linarith))
    fifth_septic_error_deriv_bound_final (fun x hx => fifth_septic_error_axes x (by linarith)) w hw

theorem fifth_septic_remainder_bounds (z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 1/2 ≤ z.re^2) :
    let U := z.re^2+z.im^2
    0 < (fifthSepticRemainder z).re/z.re ∧ (fifthSepticRemainder z).re/z.re ≤ (263/2000)/U ∧
      -(263/2000)/U ≤ (fifthSepticRemainder z).im/z.im ∧ (fifthSepticRemainder z).im/z.im < 0 := by
  have hU : 1/2 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0 < z.re^2+z.im^2 := by linarith
  have hn : ‖z⁻¹‖^2 ≤ 2 := by
    rw [norm_inv,inv_pow,Complex.sq_norm,Complex.normSq_apply]
    apply (inv_le_comm₀ (by nlinarith) (by norm_num)).mpr
    norm_num
    nlinarith
  obtain ⟨hAlo,hAhi,hBlo,hBhi⟩ := inverse_error_coordinate_bounds fifthSepticError fifthSepticLeadingError
    (7/125) z hx hy (fifth_septic_error_coordinates z⁻¹ hn)
  obtain ⟨hgl,hgu⟩ := fifth_septic_leading_bounds
  have hp : 0 < (fifthSepticLeadingError-7/125)/(z.re^2+z.im^2) := div_pos (by linarith) hUp
  have hu : (fifthSepticLeadingError+7/125)/(z.re^2+z.im^2) ≤ (263/2000)/(z.re^2+z.im^2) :=
    div_le_div_of_nonneg_right (by linarith) hUp.le
  change 0 < _ ∧ _ ≤ _ ∧ _ ≤ _ ∧ _ < _
  change (fifthSepticLeadingError-7/125)/_ ≤ (fifthSepticRemainder z).re/z.re at hAlo
  change (fifthSepticRemainder z).re/z.re ≤ _ at hAhi
  change _ ≤ (fifthSepticRemainder z).im/z.im at hBlo
  change (fifthSepticRemainder z).im/z.im ≤ _ at hBhi
  simp only [neg_div] at hBlo hBhi ⊢
  exact ⟨lt_of_lt_of_le hp hAlo,hAhi.trans hu,by linarith,by linarith⟩
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticScalars

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_septic_scalar_gaps :
    (29/10:ℝ) < (55-3*Real.sqrt 209)/4 ∧ (55-3*Real.sqrt 209)/4 < 3 ∧
    (12/5:ℝ) < 55-3*Real.sqrt 1122/2 ∧ (55-3*Real.sqrt 209)/4 < 55-3*Real.sqrt 1122/2 ∧
    (5/8:ℝ) < (10-15*Real.sqrt 1122/68)-(5-4*Real.sqrt 209/19) ∧
    (263/1000:ℝ) < (5-4*Real.sqrt 209/19)-(29/50)*((55-3*Real.sqrt 209)/4) ∧
    (237/1160:ℝ) < (5-4*Real.sqrt 209/19)-(3/5)*((55-3*Real.sqrt 209)/4) ∧
    (24:ℝ) < (55+3*Real.sqrt 209)/4 ∧ (5+4*Real.sqrt 209/19) < 9 := by
  have h1 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
  have p1 := Real.sqrt_nonneg 209
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1122)
  have p2 := Real.sqrt_nonneg 1122
  have l1 : (144568:ℝ)/10000 < Real.sqrt 209 := by nlinarith only [h1,p1]
  have u1 : Real.sqrt 209 < (144569:ℝ)/10000 := by nlinarith only [h1,p1]
  have l2 : (334962:ℝ)/10000 < Real.sqrt 1122 := by nlinarith only [h2,p2]
  have u2 : Real.sqrt 1122 < (334963:ℝ)/10000 := by nlinarith only [h2,p2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [l1,u1,l2,u2]
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticLocalization

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem inverse_norm_square_bound (z : ℂ) (T : ℝ) (hT : 0 < T) (hX : T ≤ z.re^2) :
    ‖z⁻¹‖^2 ≤ T⁻¹ := by
  have hnorm : T ≤ ‖z‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  rw [norm_inv,inv_pow]
  exact inv_anti₀ hT hnorm

theorem fifth_septic_selected_localization (β z : ℂ) (hR : 0 ≤ β.re)
    (hx : 0 < z.re) (hy : 0 < z.im) (hX : 1/2 ≤ z.re^2)
    (hg : β/z = (((55-3*Real.sqrt 209)/4:ℝ):ℂ)*z^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder z/z) :
    3/5 < z.re^2 ∧ (3*((fifthSepticRemainder z).re/z.re)-(fifthSepticRemainder z).im/z.im)/2 ≤ 39/100 := by
  let α := (55-3*Real.sqrt 209)/4
  let b := 5-4*Real.sqrt 209/19
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hr := (cubic_graph_coordinate_parts β z (fifthSepticRemainder z) α b hz hg).1
  have hRp : β.re/z.re = α*(z.re^2-3*z.im^2)-b+(fifthSepticRemainder z).re/z.re := by rw [hr]; field_simp
  have hR0 : 0 ≤ β.re/z.re := div_nonneg hR hx.le
  rw [hRp] at hR0
  obtain ⟨ha,_,_,_,_,hloc1,hloc2,_,_⟩ := fifth_septic_scalar_gaps
  change (29/10:ℝ) < α at ha
  change (263/1000:ℝ) < b-(29/50)*α at hloc1
  change (237/1160:ℝ) < b-(3/5)*α at hloc2
  have hterm := mul_nonneg (show 0 ≤ α by linarith only [ha]) (sq_nonneg z.im)
  have hUp : 0 < z.re^2+z.im^2 := by positivity
  obtain ⟨_,hA,_,_⟩ := fifth_septic_remainder_bounds z hx hy hX
  have hU : 1/2 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hA1 : (fifthSepticRemainder z).re/z.re ≤ 263/1000 := by
    apply hA.trans
    apply (div_le_iff₀ hUp).mpr
    linarith only [hU]
  have hX1 : 29/50 < z.re^2 := by
    have ht : α*(29/50) < α*z.re^2 := by nlinarith only [hR0,hterm,hA1,hloc1]
    exact lt_of_mul_lt_mul_left ht (by linarith only [ha])
  have hn1 : ‖z⁻¹‖^2 ≤ 50/29 := by
    convert inverse_norm_square_bound z (29/50) (by norm_num) hX1.le using 1 <;> norm_num
  obtain ⟨_,hA2,_,_⟩ := inverse_error_coordinate_bounds fifthSepticError fifthSepticLeadingError
    (43/1000) z hx hy (fifth_septic_error_coordinates_refined z⁻¹ hn1)
  change (fifthSepticRemainder z).re/z.re ≤ _ at hA2
  have hgu := fifth_septic_leading_bounds.2
  have hA2' : (fifthSepticRemainder z).re/z.re ≤ 237/1160 := by
    apply hA2.trans
    apply (div_le_iff₀ hUp).mpr
    nlinarith only [hX1,hgu,sq_nonneg z.im]
  have hX2 : 3/5 < z.re^2 := by
    have ht : α*(3/5) < α*z.re^2 := by nlinarith only [hR0,hterm,hA2',hloc2]
    exact lt_of_mul_lt_mul_left ht (by linarith only [ha])
  refine ⟨hX2,?_⟩
  have hn2 : ‖z⁻¹‖^2 ≤ 5/3 := by
    convert inverse_norm_square_bound z (3/5) (by norm_num) hX2.le using 1 <;> norm_num
  obtain ⟨_,hA3,hB3,_⟩ := inverse_error_coordinate_bounds fifthSepticError fifthSepticLeadingError
    (1/25) z hx hy (fifth_septic_error_coordinates_final z⁻¹ hn2)
  change (fifthSepticRemainder z).re/z.re ≤ _ at hA3
  change _ ≤ (fifthSepticRemainder z).im/z.im at hB3
  have hc : (fifthSepticLeadingError+1/25)/(z.re^2+z.im^2) ≤ 39/200 := by
    apply (div_le_iff₀ hUp).mpr
    nlinarith only [hX2,hgu,sq_nonneg z.im]
  simp only [neg_div] at hB3
  linarith only [hA3,hB3,hc]
end DerivativeChainPrivate

end


section
-- Source module: FifthMiddleBounds

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_septic_selected_bounds (β z : ℂ) (hR : 0 ≤ β.re) (hx : 0 < z.re) (hy : 0 < z.im)
    (hX : 3/5 ≤ z.re^2)
    (hg : β/z = (((55-3*Real.sqrt 209)/4:ℝ):ℂ)*z^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder z/z) :
    (fifthSepticRemainder z).re/z.re ≤ 39/200 ∧ (fifthSepticRemainder z).im/z.im ≤ 0 ∧
      (3*((fifthSepticRemainder z).re/z.re)-(fifthSepticRemainder z).im/z.im)/2 ≤ 39/100 ∧
      3/5 ≤ z.re^2-3*z.im^2 := by
  have hXlo : 1/2 ≤ z.re^2 := by linarith only [hX]
  have hloc := fifth_septic_selected_localization β z hR hx hy hXlo hg
  have hB := (fifth_septic_remainder_bounds z hx hy hXlo).2.2.2
  have hn : ‖z⁻¹‖^2 ≤ 5/3 := by
    convert inverse_norm_square_bound z (3/5) (by norm_num) hX using 1 <;> norm_num
  have hA := (inverse_error_coordinate_bounds fifthSepticError fifthSepticLeadingError (1/25) z hx hy
    (fifth_septic_error_coordinates_final z⁻¹ hn)).2.1
  change (fifthSepticRemainder z).re/z.re ≤ _ at hA
  have hUp : 0 < z.re^2+z.im^2 := by positivity
  have hAu : (fifthSepticRemainder z).re/z.re ≤ 39/200 := by
    apply hA.trans
    apply (div_le_iff₀ hUp).mpr
    have hgu := fifth_septic_leading_bounds.2
    nlinarith only [hX,hgu,sq_nonneg z.im]
  refine ⟨hAu,hB.le,hloc.2,?_⟩
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hr := (cubic_graph_coordinate_parts β z (fifthSepticRemainder z) _ _ hz hg).1
  have hh : 0 ≤ β.re/z.re := div_nonneg hR hx.le
  have hRp : β.re/z.re = (55-3*Real.sqrt 209)/4*(z.re^2-3*z.im^2)-(5-4*Real.sqrt 209/19)+(fifthSepticRemainder z).re/z.re := by rw [hr]; field_simp
  rw [hRp] at hh
  have hslack := fifth_septic_scalar_gaps.2.2.2.2.2.2.1
  have ha := fifth_septic_scalar_gaps.1
  have ht : ((55-3*Real.sqrt 209)/4)*(3/5) < ((55-3*Real.sqrt 209)/4)*(z.re^2-3*z.im^2) := by linarith only [hh,hAu,hslack]
  exact (lt_of_mul_lt_mul_left ht (by linarith only [ha])).le


end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (β w E₀ : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 1/2 ≤ w.re^2)
    (hwroot : (2/1001)*β^2-(20/91)*β*w^3+(40/1001)*β*w+w^6-(5/7)*w^4+(10/91)*w^2-2/1001=0)
    (hwinv : β/w = ((55-3*Real.sqrt 1122/2:ℝ):ℂ)*w^2-((10-15*Real.sqrt 1122/68:ℝ):ℂ)+E₀/w)
    (hA₀hi : E₀.re/w.re ≤ 2821/12500) (hB₀hi : E₀.im/w.im ≤ 0)
    (hC₀hi : (3*(E₀.re/w.re)-E₀.im/w.im)/2 ≤ 5/8)
    (hWedge : 1/2 ≤ w.re^2-3*w.im^2) :
    ∃ z : ℂ,
      (2/143)*β^2*z-(5/13)*β*z^4+(20/143)*β*z^2-(2/429)*β+
        z^7-z^5+(10/39)*z^3-(2/143)*z=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 3/5 < z.re^2 ∧
      β/z = (((55-3*Real.sqrt 209)/4:ℝ):ℂ)*z^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder z/z ∧
      (fifthSepticRemainder z).re/z.re ≤ 39/200 ∧ (fifthSepticRemainder z).im/z.im ≤ 0 ∧
      (3*((fifthSepticRemainder z).re/z.re)-(fifthSepticRemainder z).im/z.im)/2 ≤ 39/100 ∧
      3/5 ≤ z.re^2-3*z.im^2 := by
  obtain ⟨z,hz,hr,hi,hg⟩ := normalized_fifth_septic_step β w E₀ hR hI hwpos hwim hwX hwroot hwinv hA₀hi hB₀hi hC₀hi hWedge
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hr
  have hy : 0 < z.im := lt_of_lt_of_le hwim hi
  have hX : 1/2 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hr]
  have hl := (fifth_septic_selected_localization β z hR hx hy hX hg).1
  obtain ⟨ha,hb,hc,hw⟩ := fifth_septic_selected_bounds β z hR hx hy hl.le hg
  exact ⟨z,hz,hr,hi,hl,hg,ha,hb,hc,hw⟩
