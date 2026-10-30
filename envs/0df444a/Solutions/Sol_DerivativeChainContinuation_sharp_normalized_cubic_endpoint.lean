-- Prove2me | solution 1 for DerivativeChainContinuation.sharp_normalized_cubic_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:34:17.491633+00:00
-- url     : https://prove2.me/submissions/87c96a75-482d-4bd0-bfc8-276b42df3818

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainContinuation_SharpCubicTriangle
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_cubicTriangle_endpoint_budget
import Theorems.Thm_DerivativeChainContinuation_cubic_endpoint_parameters
import Theorems.Thm_DerivativeChainContinuation_exists_oriented_square_root
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


set_option autoImplicit false
namespace DerivativeChainContinuation



theorem sharpCubicConstant_positive : 0 < sharpCubicConstant := by
  unfold sharpCubicConstant
  positivity









end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (A : ℝ) (hA : 0 ≤ A) (B a o : ℂ)
    (hBR : 0 ≤ B.re) (hBI : 0 ≤ B.im) (ha : a^3-(A:ℂ)*a-B=0)
    (hx : 0 ≤ a.re) (hy : 0 ≤ a.im) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z : ℂ, z^3-(A:ℂ)*z-B=0 → ‖z-o‖ ≤ R) :
    a.re+a.im ≤ sharpCubicConstant*R := by
  by_cases hx0 : a.re=0
  · have hi := congrArg Complex.im ha
    simp [pow_succ, pow_two, Complex.mul_im, Complex.mul_re, hx0] at hi
    have hy0 : a.im=0 := by
      have hh := mul_nonneg hA hy
      have hh' := mul_nonneg (sq_nonneg a.im) hy
      by_contra hyne
      have hyp : 0 < a.im := lt_of_le_of_ne hy (Ne.symm hyne)
      have hhpos := pow_pos hyp 3
      nlinarith
    rw [hx0,hy0,add_zero]
    exact mul_nonneg sharpCubicConstant_positive.le hR
  have hxp : 0 < a.re := lt_of_le_of_ne hx (Ne.symm hx0)
  have hxn : (a.re:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
  obtain ⟨d,hd,hdr,hdi⟩ := exists_oriented_square_root ((A:ℂ)-(3/4)*a^2)
  have hAc : (3/4)*a^2+d^2=(A:ℂ) := by linear_combination hd
  have hBc : a^3/4-a*d^2=B := by linear_combination ha-a*hd
  have hAr := congrArg Complex.re hAc
  have hAi := congrArg Complex.im hAc
  have hBr := congrArg Complex.re hBc
  simp [pow_succ, pow_two, Complex.mul_re, Complex.mul_im] at hAr hAi hBr
  have hrel : d.re*d.im=-(3/4)*a.re*a.im := by nlinarith [hAi]
  have hAA : 0 ≤ (3/4)*(a.re^2-a.im^2)+d.re^2-d.im^2 := by nlinarith [hAr]
  have hBB : 0 ≤ a.re^3/4-3*a.re*a.im^2/4-a.re*d.re^2+a.re*d.im^2+
      2*a.im*d.re*d.im := by nlinarith [hBr]
  obtain ⟨k,s,hk,hk1,hs,hs3,hyr,hur,hvr⟩ :=
    cubic_endpoint_parameters a.re a.im d.re d.im hxp hy hdr hdi hrel hAA hBB
  let b := -a/2+d
  let c := -a/2-d
  have hb : b^3-(A:ℂ)*b-B=0 := by rw [← hAc,← hBc]; dsimp [b]; ring
  have hc : c^3-(A:ℂ)*c-B=0 := by rw [← hAc,← hBc]; dsimp [c]; ring
  have hpa : a=(a.re:ℂ)*cubicTriangleA k s := by
    apply Complex.ext <;> simp [cubicTriangleA,Complex.mul_re,Complex.mul_im]
    nlinarith [hyr]
  have hpb : b=(a.re:ℂ)*cubicTriangleB k s := by
    apply Complex.ext <;> simp [b,cubicTriangleB,Complex.mul_re,Complex.mul_im,
      Complex.div_re,Complex.div_im] <;> nlinarith [hyr,hur,hvr]
  have hpc : c=(a.re:ℂ)*cubicTriangleC k s := by
    apply Complex.ext <;> simp [c,cubicTriangleC,Complex.mul_re,Complex.mul_im,
      Complex.div_re,Complex.div_im] <;> nlinarith [hyr,hur,hvr]
  have hnorm (z t : ℂ) (hz : z=(a.re:ℂ)*t) (hroot : z^3-(A:ℂ)*z-B=0) :
      ‖t-o/(a.re:ℂ)‖ ≤ R/a.re := by
    have he : t-o/(a.re:ℂ)=(z-o)/(a.re:ℂ) := by rw [hz]; field_simp [hxn] <;> ring
    rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxp]
    exact div_le_div_of_nonneg_right (hbound z hroot) hxp.le
  have hmetric := cubicTriangle_endpoint_budget k s hk hk1 hs hs3 (o/(a.re:ℂ))
    (R/a.re) (div_nonneg hR hxp.le) (hnorm a _ hpa ha) (hnorm b _ hpb hb) (hnorm c _ hpc hc)
  calc
    a.re+a.im = a.re*(1+k*s/3) := by rw [hyr]; ring
    _ ≤ a.re*(sharpCubicConstant*(R/a.re)) := mul_le_mul_of_nonneg_left hmetric hxp.le
    _ = sharpCubicConstant*R := by field_simp
