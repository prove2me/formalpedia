-- Prove2me | solution 1 for DerivativeChainContinuation.finite_weighted_complex_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:14:29.111389+00:00
-- url     : https://prove2.me/submissions/493185fb-6846-474b-b446-cd473c2c28b2

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators


theorem solution {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a : ι → ℂ) (hw : ∀ i,0 ≤ w i) :
    Complex.normSq (∑ i,(w i:ℂ)*a i) ≤ (∑ i,w i)*(∑ i,w i*Complex.normSq (a i)) := by
  have hreal (f : ι → ℝ) : (∑ i,w i*f i)^2 ≤ (∑ i,w i)*(∑ i,w i*(f i)^2) := by
    have h1 (i : ι) : Real.sqrt (w i)*(Real.sqrt (w i)*f i)=w i*f i := by
      rw [← mul_assoc,← pow_two,Real.sq_sqrt (hw i)]
    have h2 (i : ι) : (Real.sqrt (w i)*f i)^2=w i*(f i)^2 := by
      rw [mul_pow,Real.sq_sqrt (hw i)]
    simpa only [h1,h2,Real.sq_sqrt (hw _)] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (w i))
        (fun i => Real.sqrt (w i)*f i)
  have hr := hreal (fun i => (a i).re)
  have hi := hreal (fun i => (a i).im)
  simp only [Complex.normSq_apply,Complex.re_sum,Complex.im_sum,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero,
    ← pow_two,mul_add,Finset.sum_add_distrib]
  nlinarith
