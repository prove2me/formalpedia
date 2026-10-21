-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fifth_octic_step_with_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T23:06:58.442878+00:00
-- url     : https://prove2.me/submissions/f4854a27-da58-40c9-a696-bf737d28aee4

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_octic_step
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
-- Source module: FifthOcticAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators














theorem fifth_octic_poly_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) : ‖fifthOcticPoly u-1‖ ≤ 1/2 := by
  have hs := norm_real_power_sum_le fifthOcticCoeffs u (9/4) (by norm_num) hu
  calc
    _ = ‖u‖*‖∑ i : Fin 16, (fifthOcticCoeffs i:ℂ)*u^i.val‖ := by simp [fifthOcticPoly,norm_mul]
    _ ≤ (9/4)*(∑ i : Fin 16, |fifthOcticCoeffs i| *(9/4:ℝ)^i.val) := mul_le_mul hu hs (norm_nonneg _) (by norm_num)
    _ ≤ 1/2 := by norm_num [fifthOcticCoeffs,Fin.sum_univ_succ]

theorem fifth_octic_residual_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) : ‖fifthOcticResidual u‖ ≤ 1/10000000000000 := by
  apply (norm_real_power_sum_le fifthOcticResidualCoeffs u (9/4) (by norm_num) hu).trans
  norm_num [fifthOcticResidualCoeffs,Fin.sum_univ_succ]
theorem fifth_octic_coefficient_bounds :
    (57/1000:ℝ) < fifthOcticExpansionCoeffs 0 ∧ fifthOcticExpansionCoeffs 0 < 3/50 ∧
    |fifthOcticRationalTailCoeff| ≤ 651/500000000000000000 ∧
    ∀ i : Fin 14, |fifthOcticErrorCoeffs i| ≤ fifthOcticErrorCoeffBounds i := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 22)
  have hp := Real.sqrt_nonneg 22
  have hl : (4690415759/1000000000:ℝ) ≤ Real.sqrt 22 := by nlinarith only [hs,hp]
  have hu : Real.sqrt 22 ≤ (58630197/12500000:ℝ) := by nlinarith only [hs,hp]
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [fifthOcticExpansionCoeffs]; linarith only [hl,hu]
  · norm_num [fifthOcticExpansionCoeffs]; linarith only [hl,hu]
  · rw [abs_le]; dsimp [fifthOcticRationalTailCoeff]; constructor <;> linarith only [hl,hu]
  · intro i
    fin_cases i <;> norm_num [fifthOcticErrorCoeffs,fifthOcticErrorCoeffBounds,abs_le] <;> constructor <;> linarith only [hl,hu]
end DerivativeChainPrivate

end


section
-- Source module: FifthOcticSlit

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_octic_radicand_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    ‖fifthOcticRadicand u-1‖ ≤ 3/4 := by
  have he : fifthOcticRadicand u-1 = -(1/4:ℂ)*u+(1/66:ℂ)*u^2+(1/1188:ℂ)*u^3 := by
    dsimp [fifthOcticRadicand]; ring
  rw [he]
  calc
    _ ≤ ‖-(1/4:ℂ)*u‖+‖(1/66:ℂ)*u^2‖+‖(1/1188:ℂ)*u^3‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (1/4:ℝ)*‖u‖+(1/66:ℝ)*‖u‖^2+(1/1188:ℝ)*‖u‖^3 := by norm_num [norm_mul,norm_pow]
    _ ≤ (1/4:ℝ)*(9/4)+(1/66:ℝ)*(9/4)^2+(1/1188:ℝ)*(9/4)^3 := by gcongr
    _ ≤ 3/4 := by norm_num

theorem fifth_octic_slit (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    fifthOcticRadicand u ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hn := fifth_octic_radicand_bound u hu
  have hr := Complex.re_le_norm (1-fifthOcticRadicand u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re,Complex.one_re] at hr
  linarith

theorem fifth_octic_denominator_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    Complex.sqrt (fifthOcticRadicand u)+fifthOcticPoly u ≠ 0 ∧
      ‖(Complex.sqrt (fifthOcticRadicand u)+fifthOcticPoly u)⁻¹‖ ≤ 2 := by
  have hs : 0 ≤ (Complex.sqrt (fifthOcticRadicand u)).re := by
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hp := fifth_octic_poly_bound u hu
  have hr := Complex.re_le_norm (1-fifthOcticPoly u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re,Complex.one_re] at hr
  have hd := Complex.re_le_norm (Complex.sqrt (fifthOcticRadicand u)+fifthOcticPoly u)
  simp only [Complex.add_re] at hd
  have hl : (1/2:ℝ) ≤ ‖Complex.sqrt (fifthOcticRadicand u)+fifthOcticPoly u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi := inv_anti₀ (by norm_num : (0:ℝ) < 1/2) hl
  norm_num at hi
  exact hi

theorem fifth_octic_pole_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    1-(1/12:ℂ)*u ≠ 0 ∧ ‖(1-(1/12:ℂ)*u)⁻¹‖ ≤ 2 := by
  have hn := norm_sub_norm_le (1:ℂ) ((1/12:ℂ)*u)
  norm_num [norm_mul] at hn
  have hl : (1/2:ℝ) ≤ ‖1-(1/12:ℂ)*u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi := inv_anti₀ (by norm_num : (0:ℝ) < 1/2) hl
  norm_num at hi
  exact hi

end DerivativeChainPrivate

end


section
-- Source module: FifthOcticTail


set_option autoImplicit false
namespace DerivativeChainPrivate



theorem fifth_octic_tail_norm (w : ℂ) (hw : ‖w‖ ≤ 3/2) : ‖fifthOcticTail w‖ ≤ 1/1000000 := by
  have hu : ‖w^2‖ ≤ 9/4 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hk : 0 < (3*Real.sqrt 22/4:ℝ) := by positivity
  have hku : (3*Real.sqrt 22/4:ℝ) ≤ 18/5 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 22)
    have hp := Real.sqrt_nonneg 22
    nlinarith
  have hf : ‖1-(1/3:ℂ)*w^2‖ ≤ 7/4 := by
    calc
      _ ≤ ‖(1:ℂ)‖+‖(1/3:ℂ)*w^2‖ := norm_sub_le _ _
      _ = 1+(1/3:ℝ)*‖w^2‖ := by norm_num [norm_mul]
      _ ≤ 7/4 := by linarith
  have ht := fifth_octic_residual_bound (w^2) hu
  have hd := (fifth_octic_denominator_bound (w^2) hu).2
  have hp := (fifth_octic_pole_bound (w^2) hu).2
  have hL : |fifthOcticRationalTailCoeff| ≤ 1/100000000000000 := by
    have hh := fifth_octic_coefficient_bounds.2.2.1
    linarith only [hh]
  have h1 : ‖(fifthOcticRationalTailCoeff:ℂ)*w^31/(1-(1/12:ℂ)*w^2)‖ ≤ (1/100000000000000:ℝ)*(3/2)^31*2 := by
    calc
      _ = |fifthOcticRationalTailCoeff| * ‖w‖^31*‖(1-(1/12:ℂ)*w^2)⁻¹‖ := by
        simp [div_eq_mul_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ _ := by gcongr
  have h2 : ‖((3*Real.sqrt 22/4:ℝ):ℂ)*w^31*(1-(1/3:ℂ)*w^2)*fifthOcticResidual (w^2)/
      (Complex.sqrt (fifthOcticRadicand (w^2))+fifthOcticPoly (w^2))/(1-(1/12:ℂ)*w^2)‖ ≤
      (18/5:ℝ)*(3/2)^31*(7/4)*(1/10000000000000)*2*2 := by
    calc
      _ = (3*Real.sqrt 22/4:ℝ)*‖w‖^31*‖1-(1/3:ℂ)*w^2‖*‖fifthOcticResidual (w^2)‖*
          ‖(Complex.sqrt (fifthOcticRadicand (w^2))+fifthOcticPoly (w^2))⁻¹‖*‖(1-(1/12:ℂ)*w^2)⁻¹‖ := by
        simp only [div_eq_mul_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
        norm_num [abs_of_nonneg (Real.sqrt_nonneg 22)]
      _ ≤ _ := by gcongr
  unfold fifthOcticTail
  apply (norm_sub_le _ _).trans
  have hh := add_le_add h1 h2
  apply hh.trans
  norm_num

theorem fifth_octic_tail_differentiableAt (w : ℂ) (hw : ‖w‖ ≤ 3/2) :
    DifferentiableAt ℂ fifthOcticTail w := by
  have hu : ‖w^2‖ ≤ 9/4 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hh : DifferentiableAt ℂ (fun v : ℂ => fifthOcticRadicand (v^2)) w := by
    unfold fifthOcticRadicand
    fun_prop
  have hs : DifferentiableAt ℂ (fun v : ℂ => Complex.sqrt (fifthOcticRadicand (v^2))) w := by
    simpa only [Function.comp_def] using
      (Complex.differentiableAt_sqrt (fifth_octic_slit (w^2) hu)).comp w hh
  have hpoly : DifferentiableAt ℂ (fun v : ℂ => fifthOcticPoly (v^2)) w := by unfold fifthOcticPoly; fun_prop
  have ht : DifferentiableAt ℂ (fun v : ℂ => fifthOcticResidual (v^2)) w := by unfold fifthOcticResidual; fun_prop
  have hd := (fifth_octic_denominator_bound (w^2) hu).1
  have hp := (fifth_octic_pole_bound (w^2) hu).1
  unfold fifthOcticTail
  fun_prop

theorem fifth_octic_tail_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    ‖deriv fifthOcticTail w‖ ≤ 1/25000 := by
  have hw' : ‖w‖ ≤ 29/20 := by nlinarith [norm_nonneg w]
  have hball : ∀ u ∈ Metric.ball w (1/20:ℝ), ‖u‖ ≤ 3/2 := by
    intro u hu
    have hd : ‖u-w‖ < 1/20 := by simpa only [Metric.mem_ball,dist_eq_norm] using hu
    have hn := norm_le_norm_sub_add u w
    linarith
  have hd : DifferentiableOn ℂ fifthOcticTail (Metric.ball w (1/20:ℝ)) := by
    intro u hu
    exact (fifth_octic_tail_differentiableAt u (hball u hu)).differentiableWithinAt
  have hm : Set.MapsTo fifthOcticTail (Metric.ball w (1/20:ℝ))
      (Metric.closedBall (fifthOcticTail w) (1/500000:ℝ)) := by
    intro u hu
    rw [Metric.mem_closedBall,dist_eq_norm]
    have h1 := fifth_octic_tail_norm u (hball u hu)
    have h2 := fifth_octic_tail_norm w (by linarith)
    have hn := norm_sub_le (fifthOcticTail u) (fifthOcticTail w)
    linarith
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hd hm (by norm_num : (0:ℝ) < 1/20)
  norm_num at hh
  exact hh

end DerivativeChainPrivate

end


section
-- Source module: FifthOcticErrorDerivative


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open scoped BigOperators




theorem fifth_octic_polynomial_error_hasDerivAt (w : ℂ) :
    HasDerivAt fifthOcticPolynomialError
      (∑ i : Fin 14, (fifthOcticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)) w := by
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [show 2*i.val+3-1=2*i.val+2 by omega,mul_assoc] using
    (hasDerivAt_pow (2*i.val+3) w).const_mul (fifthOcticErrorCoeffs i:ℂ)

theorem fifth_octic_polynomial_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 5/3) :
    ‖deriv fifthOcticPolynomialError w‖ ≤ 29/1000 := by
  rw [(fifth_octic_polynomial_error_hasDerivAt w).deriv]
  have hsum : ‖∑ i : Fin 14, (fifthOcticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)‖ ≤
      ∑ i : Fin 14, fifthOcticErrorCoeffBounds i * ((2*i.val+3:ℕ):ℝ)*(5/3:ℝ)^(i.val+1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    rw [show 2*i.val+2=2*(i.val+1) by omega,pow_mul]
    have hb := fifth_octic_coefficient_bounds.2.2.2 i
    have hb0 : 0 ≤ fifthOcticErrorCoeffBounds i := (abs_nonneg _).trans hb
    gcongr
  apply hsum.trans
  norm_num [fifthOcticErrorCoeffBounds,Fin.sum_univ_succ]

theorem fifth_octic_error_differentiableAt (w : ℂ) (hw : ‖w‖^2 ≤ 5/3) :
    DifferentiableAt ℂ fifthOcticError w := by
  have hn : ‖w‖ ≤ 3/2 := by nlinarith [norm_nonneg w]
  exact (fifth_octic_polynomial_error_hasDerivAt w).differentiableAt.add (fifth_octic_tail_differentiableAt w hn)

theorem fifth_octic_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 5/3) :
    ‖deriv fifthOcticError w‖ ≤ 3/100 := by
  have hn : ‖w‖ ≤ 3/2 := by nlinarith [norm_nonneg w]
  have hp := fifth_octic_polynomial_error_deriv_bound w hw
  have ht := fifth_octic_tail_deriv_bound w (by linarith)
  have hd : deriv fifthOcticError w = deriv fifthOcticPolynomialError w+deriv fifthOcticTail w := by
    exact deriv_add (fifth_octic_polynomial_error_hasDerivAt w).differentiableAt (fifth_octic_tail_differentiableAt w hn)
  rw [hd]
  have hs := norm_add_le (deriv fifthOcticPolynomialError w) (deriv fifthOcticTail w)
  linarith

end DerivativeChainPrivate

end


section
-- Source module: FifthOcticAxes


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem fifth_octic_radicand_real (x : ℝ) : fifthOcticRadicand (x:ℂ) = ((1-x/4+x^2/66+x^3/1188:ℝ):ℂ) := by
  simp [fifthOcticRadicand] <;> ring
theorem fifth_octic_poly_real (x : ℝ) : fifthOcticPoly (x:ℂ) =
    ((1+x*(∑ i : Fin 16, fifthOcticCoeffs i*x^i.val):ℝ):ℂ) := by simp [fifthOcticPoly]
theorem fifth_octic_residual_real (x : ℝ) : fifthOcticResidual (x:ℂ) =
    ((∑ i : Fin 16, fifthOcticResidualCoeffs i*x^i.val : ℝ):ℂ) := by simp [fifthOcticResidual]
theorem fifth_octic_sqrt_real (x : ℝ) (hx : |x| ≤ 9/4) : Complex.sqrt (fifthOcticRadicand (x:ℂ)) =
    ((Real.sqrt (1-x/4+x^2/66+x^3/1188):ℝ):ℂ) := by
  have hp := fifth_octic_slit (x:ℂ) (by simpa using hx)
  have hreal := fifth_octic_radicand_real x
  have hpos : 0 < (fifthOcticRadicand (x:ℂ)).re := by
    have hb := fifth_octic_radicand_bound (x:ℂ) (by simpa using hx)
    have hr := Complex.re_le_norm (1-fifthOcticRadicand (x:ℂ))
    rw [norm_sub_rev] at hr
    simp only [Complex.sub_re,Complex.one_re] at hr
    linarith
  rw [hreal,Complex.ofReal_re] at hpos
  have hp : 0 ≤ 1-x/4+x^2/66+x^3/1188 := hpos.le
  rw [fifth_octic_radicand_real,Complex.sqrt_of_nonneg (by exact_mod_cast hp),Complex.ofReal_re]

theorem fifth_octic_tail_real_axis (x : ℝ) (hx : x^2 ≤ 2) : (fifthOcticTail (x:ℂ)).im = 0 := by
  unfold fifthOcticTail
  rw [show (x:ℂ)^2 = ((x^2:ℝ):ℂ) by norm_cast]
  rw [fifth_octic_sqrt_real _ (by rw [abs_of_nonneg (sq_nonneg x)]; linarith),fifth_octic_poly_real,fifth_octic_residual_real]
  rw [show (x:ℂ)^31=((x^31:ℝ):ℂ) by norm_cast]
  rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,show (1/12:ℂ)=((1/12:ℝ):ℂ) by norm_num]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div,← Complex.ofReal_pow,Complex.ofReal_im]

theorem fifth_octic_tail_imaginary_axis (x : ℝ) (hx : x^2 ≤ 2) : (fifthOcticTail (Complex.I*(x:ℂ))).re = 0 := by
  unfold fifthOcticTail
  rw [show (Complex.I*(x:ℂ))^2 = ((-x^2:ℝ):ℂ) by norm_num [mul_pow]]
  rw [fifth_octic_sqrt_real _ (by rw [abs_neg,abs_of_nonneg (sq_nonneg x)]; linarith),fifth_octic_poly_real,fifth_octic_residual_real]
  have he : (Complex.I*(x:ℂ))^31 = -Complex.I*((x^31:ℝ):ℂ) := by
    norm_num [mul_pow,Complex.I_pow_eq_pow_mod] <;> norm_num [Complex.I_pow_three]
  rw [he]
  rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,show (1/12:ℂ)=((1/12:ℝ):ℂ) by norm_num]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div,← Complex.ofReal_pow]
  simp only [Complex.sub_re,Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,zero_add,add_zero,
    sub_zero,zero_sub,mul_one,one_mul,neg_zero,zero_div]

theorem fifth_octic_error_axes (x : ℝ) (hx : x^2 ≤ 2) :
    (fifthOcticError (x:ℂ)).im = 0 ∧ (fifthOcticError (Complex.I*(x:ℂ))).re = 0 := by
  constructor
  · rw [fifthOcticError,Complex.add_im,fifth_octic_tail_real_axis x hx,add_zero]
    norm_num [fifthOcticPolynomialError,Fin.sum_univ_succ,← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re]
  · rw [fifthOcticError,Complex.add_re,fifth_octic_tail_imaginary_axis x hx,add_zero]
    norm_num [fifthOcticPolynomialError,Fin.sum_univ_succ,mul_pow,Complex.I_pow_eq_pow_mod,
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
-- Source module: FifthOcticCoordinates

set_option autoImplicit false
namespace DerivativeChainPrivate



theorem fifth_octic_leading_bounds : (57/1000:ℝ) < fifthOcticLeadingError ∧ fifthOcticLeadingError < 3/50 :=
  ⟨fifth_octic_coefficient_bounds.1,fifth_octic_coefficient_bounds.2.1⟩

theorem fifth_octic_error_coordinates (w : ℂ) (hw : ‖w‖^2 ≤ 5/3) :
    |(fifthOcticError w).re| ≤ (3/100)*|w.re| ∧ |(fifthOcticError w).im| ≤ (3/100)*|w.im| :=
  analytic_error_coordinate_bounds fifthOcticError (5/3) (3/100)
    fifth_octic_error_differentiableAt fifth_octic_error_deriv_bound
    (fun x hx => fifth_octic_error_axes x (by linarith)) w hw

theorem fifth_octic_remainder_bounds (z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 3/5 ≤ z.re^2) :
    let U := z.re^2+z.im^2
    0 < (fifthOcticRemainder z).re/z.re ∧ (fifthOcticRemainder z).re/z.re ≤ (9/100)/U ∧
      -(9/100)/U ≤ (fifthOcticRemainder z).im/z.im ∧ (fifthOcticRemainder z).im/z.im < 0 := by
  have hU : 3/5 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0 < z.re^2+z.im^2 := by linarith
  have hn : ‖z⁻¹‖^2 ≤ 5/3 := by
    rw [norm_inv,inv_pow,Complex.sq_norm,Complex.normSq_apply]
    apply (inv_le_comm₀ (by nlinarith) (by norm_num)).mpr
    norm_num
    nlinarith
  obtain ⟨hAlo,hAhi,hBlo,hBhi⟩ := inverse_error_coordinate_bounds fifthOcticError fifthOcticLeadingError
    (3/100) z hx hy (fifth_octic_error_coordinates z⁻¹ hn)
  obtain ⟨hgl,hgu⟩ := fifth_octic_leading_bounds
  have hp : 0 < (fifthOcticLeadingError-3/100)/(z.re^2+z.im^2) := div_pos (by linarith) hUp
  have hu : (fifthOcticLeadingError+3/100)/(z.re^2+z.im^2) ≤ (9/100)/(z.re^2+z.im^2) :=
    div_le_div_of_nonneg_right (by linarith) hUp.le
  change 0 < _ ∧ _ ≤ _ ∧ _ ≤ _ ∧ _ < _
  change (fifthOcticLeadingError-3/100)/_ ≤ (fifthOcticRemainder z).re/z.re at hAlo
  change (fifthOcticRemainder z).re/z.re ≤ _ at hAhi
  change _ ≤ (fifthOcticRemainder z).im/z.im at hBlo
  change (fifthOcticRemainder z).im/z.im ≤ _ at hBhi
  simp only [neg_div] at hBlo hBhi ⊢
  exact ⟨lt_of_lt_of_le hp hAlo,hAhi.trans hu,by linarith,by linarith⟩
end DerivativeChainPrivate

end


section
-- Source module: FifthOcticScalars

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_octic_scalar_gaps :
    (19/10:ℝ) < (22-3*Real.sqrt 22)/4 ∧ (22-3*Real.sqrt 22)/4 < 2 ∧
    (39/100:ℝ) < (5-4*Real.sqrt 209/19)-(92-9*Real.sqrt 22)/32 ∧
    (3/20:ℝ) < (92-9*Real.sqrt 22)/32-(7/10)*((22-3*Real.sqrt 22)/4) ∧
    (9:ℝ) < (22+3*Real.sqrt 22)/4 ∧ (92+9*Real.sqrt 22)/32 < 17/4 ∧
    (19/10:ℝ) < 5-4*Real.sqrt 209/19 := by
  have h1 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 22)
  have p1 := Real.sqrt_nonneg 22
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
  have p2 := Real.sqrt_nonneg 209
  have l1 : (46904:ℝ)/10000 < Real.sqrt 22 := by nlinarith only [h1,p1]
  have u1 : Real.sqrt 22 < (46905:ℝ)/10000 := by nlinarith only [h1,p1]
  have l2 : (144568:ℝ)/10000 < Real.sqrt 209 := by nlinarith only [h2,p2]
  have u2 : Real.sqrt 209 < (144569:ℝ)/10000 := by nlinarith only [h2,p2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [l1,u1,l2,u2]
end DerivativeChainPrivate

end


section
-- Source module: FifthMiddleBounds

set_option autoImplicit false
namespace DerivativeChainPrivate



theorem fifth_octic_selected_bounds (β z : ℂ) (hR : 0 ≤ β.re) (hx : 0 < z.re) (hy : 0 < z.im)
    (hX : 3/5 ≤ z.re^2)
    (hg : β/z = (((22-3*Real.sqrt 22)/4:ℝ):ℂ)*z^2-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)+fifthOcticRemainder z/z) :
    7/10 < z.re^2 ∧ (fifthOcticRemainder z).re/z.re ≤ 13/100 ∧
      (fifthOcticRemainder z).im/z.im ≤ 0 ∧
      (3*((fifthOcticRemainder z).re/z.re)-(fifthOcticRemainder z).im/z.im)/2 ≤ 13/50 ∧
      7/10 ≤ z.re^2-3*z.im^2 := by
  let α := (22-3*Real.sqrt 22)/4
  let b := (92-9*Real.sqrt 22)/32
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hr := (cubic_graph_coordinate_parts β z (fifthOcticRemainder z) α b hz hg).1
  have hRp : β.re/z.re = α*(z.re^2-3*z.im^2)-b+(fifthOcticRemainder z).re/z.re := by rw [hr]; field_simp
  have hR0 : 0 ≤ β.re/z.re := div_nonneg hR hx.le
  rw [hRp] at hR0
  obtain ⟨ha,_,_,hslack,_,_,_⟩ := fifth_octic_scalar_gaps
  change (19/10:ℝ) < α at ha
  change (3/20:ℝ) < b-(7/10)*α at hslack
  have hterm := mul_nonneg (show 0 ≤ α by linarith only [ha]) (sq_nonneg z.im)
  have hUp : 0 < z.re^2+z.im^2 := by positivity
  obtain ⟨_,hA,hB,hBn⟩ := fifth_octic_remainder_bounds z hx hy hX
  have hU : 3/5 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hA1 : (fifthOcticRemainder z).re/z.re ≤ 3/20 := by
    apply hA.trans
    apply (div_le_iff₀ hUp).mpr
    linarith only [hU]
  have hX1 : 7/10 < z.re^2 := by
    have ht : α*(7/10) < α*z.re^2 := by nlinarith only [hR0,hterm,hA1,hslack]
    exact lt_of_mul_lt_mul_left ht (by linarith only [ha])
  have hc : (9/100:ℝ)/(z.re^2+z.im^2) ≤ 13/100 := by
    apply (div_le_iff₀ hUp).mpr
    nlinarith only [hX1,sq_nonneg z.im]
  refine ⟨hX1,hA.trans hc,hBn.le,?_,?_⟩
  · simp only [neg_div] at hB
    linarith only [hA,hB,hc]
  · have ht : α*(7/10) < α*(z.re^2-3*z.im^2) := by linarith only [hR0,hA1,hslack]
    exact (lt_of_mul_lt_mul_left ht (by linarith only [ha])).le
end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 3/5 ≤ w.re^2)
    (hwroot : (2/143)*β^2*w-(5/13)*β*w^4+(20/143)*β*w^2-(2/429)*β+
      w^7-w^5+(10/39)*w^3-(2/143)*w=0)
    (hwinv : β/w = (((55-3*Real.sqrt 209)/4:ℝ):ℂ)*w^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder w/w)
    (hA₀hi : (fifthSepticRemainder w).re/w.re ≤ 39/200)
    (hB₀hi : (fifthSepticRemainder w).im/w.im ≤ 0)
    (hC₀ : (3*((fifthSepticRemainder w).re/w.re)-(fifthSepticRemainder w).im/w.im)/2 ≤ 39/100)
    (hWedge : 3/5 ≤ w.re^2-3*w.im^2) :
    ∃ z : ℂ,
      z^8-(4/3)*z^6-(8/13)*β*z^5+(20/39)*z^4+(160/429)*β*z^3-(8/143)*z^2+
        (8/143)*β^2*z^2-(16/429)*β*z+1/1287-(2/429)*β^2=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 7/10 < z.re^2 ∧
      β/z = (((22-3*Real.sqrt 22)/4:ℝ):ℂ)*z^2-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)+fifthOcticRemainder z/z := by
  obtain ⟨z,hz,hr,hi,hg⟩ := normalized_fifth_octic_step β w hR hI hwpos hwim hwX hwroot hwinv hA₀hi hB₀hi hC₀ hWedge
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hr
  have hy : 0 < z.im := lt_of_lt_of_le hwim hi
  have hX : 3/5 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hr]
  have hl := (fifth_octic_selected_bounds β z hR hx hy hX hg).1
  exact ⟨z,hz,hr,hi,hl,hg⟩
