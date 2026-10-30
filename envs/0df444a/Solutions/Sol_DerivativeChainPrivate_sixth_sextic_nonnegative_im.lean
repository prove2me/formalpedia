-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_sextic_nonnegative_im
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:06:44.71588+00:00
-- url     : https://prove2.me/submissions/46592c48-7c9a-422d-bd4f-7dd8f25036e5

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_real_exterior
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_upper_data
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
open Set
namespace DerivativeChainPrivate











theorem real_quadratic_nonnegative_discriminant_root_im (A B C : ℝ)
    (hC : C ≠ 0) (hD : 0 ≤ B^2-4*A*C) (z : ℂ)
    (hroot : (A : ℂ)*z^2+(B : ℂ)*z+(C : ℂ)=0) : z.im = 0 := by
  by_contra hy
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  simp only [pow_two,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,Complex.zero_im,
    zero_mul,mul_zero,zero_add,add_zero,sub_zero] at hre him
  have hm : z.im*(2*A*z.re+B)=0 := by nlinarith only [him]
  have hl := (mul_eq_zero.mp hm).resolve_left hy
  have hA : A ≠ 0 := by
    intro ha
    rw [ha] at hl hre
    have hb : B = 0 := by simpa using hl
    apply hC
    simpa [hb] using hre
  have heq : B^2-4*A*C = -4*A^2*z.im^2 := by
    linear_combination (2*A*z.re+B)*hl-4*A*hre
  have hpos := mul_pos (sq_pos_of_ne_zero hA) (sq_pos_of_ne_zero hy)
  nlinarith only [heq,hD,hpos]





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem sixth_sextic_real_root_parameter (β : ℂ) (x : ℝ) (hx : 0 < x) (hX : 5/2 ≤ x^2)
    (hroot : (1360/91)*β^2-20*β*(x:ℂ)^3+(170/7)*β*(x:ℂ)+(x:ℂ)^6-5*(x:ℂ)^4+
      (85/16)*(x:ℂ)^2-1445/2184=0) : β.im = 0 := by
  let A : ℝ := 1360/91
  let B : ℝ := -20*x^3+(170/7)*x
  let C : ℝ := x^6-5*x^4+(85/16)*x^2-1445/2184
  have hquad : (A:ℂ)*β^2+(B:ℂ)*β+(C:ℂ)=0 := by
    dsimp [A,B,C]; push_cast; linear_combination hroot
  have hH := sixth_sextic_real_exterior (x^2) (Or.inr (by linarith))
  have hid : B^2-4*A*C = (30960/91)*x^2*(x^4+(-85/43)*x^2+1445/1806+(24565/211302)/x^2) := by
    dsimp [A,B,C]
    field_simp
    ring
  have hd : 0 ≤ B^2-4*A*C := by
    rw [hid]
    have hh : 0 < x^4+(-85/43)*x^2+1445/1806+(24565/211302)/x^2 := by
      convert hH using 1 <;> ring
    positivity
  by_cases hC : C ≠ 0
  · exact real_quadratic_nonnegative_discriminant_root_im A B C hC hd β hquad
  · have hC0 := not_ne_iff.mp hC
    rw [hC0,Complex.ofReal_zero,add_zero] at hquad
    have hp : β*((A:ℂ)*β+(B:ℂ))=0 := by linear_combination hquad
    rcases mul_eq_zero.mp hp with he|he
    · simp [he]
    · have hi := congrArg Complex.im he
      norm_num [A] at hi
      linarith



end DerivativeChainPrivate

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hx : 0 < z.re) (hX : 5/2 ≤ z.re^2)
    (hroot : (1360/91)*β^2-20*β*z^3+(170/7)*β*z+z^6-5*z^4+(85/16)*z^2-1445/2184=0) :
    0 ≤ z.im ∧ (β.im = 0 ↔ z.im = 0) := by
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hnonneg : 0 ≤ z.im := by
    by_contra h
    have hy : z.im < 0 := lt_of_not_ge h
    have hroot' : (1360/91)*(starRingEnd ℂ β)^2-20*(starRingEnd ℂ β)*(starRingEnd ℂ z)^3+
        (170/7)*(starRingEnd ℂ β)*(starRingEnd ℂ z)+(starRingEnd ℂ z)^6-5*(starRingEnd ℂ z)^4+
        (85/16)*(starRingEnd ℂ z)^2-1445/2184=0 := by
      simpa only [map_sub,map_add,map_mul,map_pow,map_div₀,map_ofNat,map_zero] using congrArg (starRingEnd ℂ) hroot
    obtain ⟨α,b,e,_,_,hp,_⟩ := sixth_sextic_upper_data μ hsupp hμ (starRingEnd ℂ β)
      (starRingEnd ℂ z) (by simpa using hx) (by simpa using neg_pos.mpr hy) (by simpa using hX) hroot'
    have hrat : 0 ≤ (β/z).im := by
      rw [Complex.div_im,← sub_div]
      apply div_nonneg
      · have h1 := mul_nonneg hI hx.le
        have h2 := mul_nonpos_of_nonneg_of_nonpos hR hy.le
        linarith
      · exact Complex.normSq_nonneg z
    have he : (starRingEnd ℂ β)/(starRingEnd ℂ z) = starRingEnd ℂ (β/z) := by simp
    rw [he,Complex.conj_im] at hp
    linarith
  refine ⟨hnonneg,?_⟩
  constructor
  · intro hβ
    by_contra hzero
    have hy : 0 < z.im := lt_of_le_of_ne hnonneg (Ne.symm hzero)
    obtain ⟨α,b,e,_,_,hp,_⟩ := sixth_sextic_upper_data μ hsupp hμ β z hx hy hX hroot
    have hn : (β/z).im ≤ 0 := by
      rw [Complex.div_im,← sub_div,hβ,zero_mul,zero_sub]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hR hy.le]) (Complex.normSq_nonneg z)
    linarith
  · intro hy
    have he : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hy]
    rw [he] at hroot
    exact sixth_sextic_real_root_parameter β z.re hx hX hroot
