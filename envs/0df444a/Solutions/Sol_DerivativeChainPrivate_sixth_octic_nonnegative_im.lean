-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_nonnegative_im
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:11:19.294972+00:00
-- url     : https://prove2.me/submissions/f13ca927-732f-4348-8afd-75ff43f2ecdb

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthOcticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_real_positive
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_tail_imaginary_axis
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_upper_data
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_upper_graphs
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

theorem solution (β z : ℂ) (hR : 0≤β.re) (hI : 0≤β.im)
    (hx : 0<z.re) (hX : 4≤z.re^2)
    (hroot : (5440/13)*β^2*z^2-(92480/429)*β^2-56*β*z^5+(680/3)*β*z^3-(5780/39)*β*z+
      z^8-(28/3)*z^6+(595/24)*z^4-(1445/78)*z^2+24565/13728=0) :
    0≤z.im ∧ (β.im=0 ↔ z.im=0) := by
  have hnonneg : 0≤z.im := by
    by_contra hn
    have hy : z.im<0 := lt_of_not_ge hn
    have hroot' : (5440/13)*(starRingEnd ℂ β)^2*(starRingEnd ℂ z)^2-
        (92480/429)*(starRingEnd ℂ β)^2-56*(starRingEnd ℂ β)*(starRingEnd ℂ z)^5+
        (680/3)*(starRingEnd ℂ β)*(starRingEnd ℂ z)^3-(5780/39)*(starRingEnd ℂ β)*(starRingEnd ℂ z)+
        (starRingEnd ℂ z)^8-(28/3)*(starRingEnd ℂ z)^6+(595/24)*(starRingEnd ℂ z)^4-
        (1445/78)*(starRingEnd ℂ z)^2+24565/13728=0 := by
      simpa only [map_sub,map_add,map_mul,map_pow,map_div₀,map_ofNat,map_zero,map_one] using congrArg (starRingEnd ℂ) hroot
    obtain ⟨α,b,e,_,_,hp,_⟩:=sixth_octic_upper_data (starRingEnd ℂ β) (starRingEnd ℂ z)
      (by simpa using hx) (by simpa using neg_pos.mpr hy) (by simpa using hX) hroot'
    have hrat : 0≤(β/z).im := by
      rw [Complex.div_im,←sub_div]
      apply div_nonneg
      · have h1:=mul_nonneg hI hx.le
        have h2:=mul_nonpos_of_nonneg_of_nonpos hR hy.le
        linarith
      · exact Complex.normSq_nonneg z
    have he : (starRingEnd ℂ β)/(starRingEnd ℂ z)=starRingEnd ℂ (β/z) := by simp
    rw [he,Complex.conj_im] at hp
    linarith
  refine ⟨hnonneg,?_⟩
  constructor
  · intro hβ
    by_contra hzero
    have hy : 0<z.im := lt_of_le_of_ne hnonneg (Ne.symm hzero)
    obtain ⟨α,b,e,_,_,hp,_⟩:=sixth_octic_upper_data β z hx hy hX hroot
    have hn : (β/z).im≤0 := by
      rw [Complex.div_im,←sub_div,hβ,zero_mul,zero_sub]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hR hy.le]) (Complex.normSq_nonneg z)
    linarith
  · intro hy
    have he : z=(z.re:ℂ) := by apply Complex.ext <;> simp [hy]
    rw [he] at hroot
    have hn : (z.re⁻¹)^2≤1/4 := by
      rw [inv_pow]
      exact (inv_le_comm₀ (sq_pos_of_pos hx) (by norm_num)).mpr (by norm_num; exact hX)
    have heIm : (sixthOcticRemainder (z.re:ℂ)).im=0 := by
      unfold sixthOcticRemainder
      rw [←Complex.ofReal_inv,Complex.add_im,(sixth_octic_error_axes _ hn).1]
      simp
    rcases sixth_octic_upper_graphs β (z.re:ℂ) (by simpa using hx) (by simpa using hX) hroot with hm|hp
    · have hi:=congrArg Complex.im hm
      simp [Complex.div_im,heIm,←Complex.ofReal_pow] at hi
      exact hi.resolve_right hx.ne'
    · have hi:=congrArg Complex.im hp
      simp [Complex.div_im,heIm,←Complex.ofReal_pow] at hi
      exact hi.resolve_right hx.ne'
