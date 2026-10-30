-- Prove2me | solution 1 for DerivativeChainContinuation.finite_weighted_variance
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:40:30.751524+00:00
-- url     : https://prove2.me/submissions/b2dfe145-7980-4db7-9ad4-293abfd35b47

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators


theorem solution {ι : Type} [Fintype ι]
    (w : ι → ℝ) (v : ι → ℂ) (z u : ℂ) (hs : ∑ i, w i=1)
    (hm : ∑ i, (w i:ℂ)*v i=z) :
    (∑ i, w i*‖v i-u‖^2)=‖z-u‖^2+(∑ i, w i*‖v i-z‖^2) := by
  have hr := congrArg Complex.re hm
  have hi := congrArg Complex.im hm
  simp only [Complex.re_sum,Complex.im_sum,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero] at hr hi
  have hpoint (i : ι) : w i*‖v i-u‖^2 = w i*‖v i-z‖^2 +
      2*(z.re-u.re)*(w i*(v i).re)+2*(z.im-u.im)*(w i*(v i).im)+
      (‖u‖^2-‖z‖^2)*w i := by
    simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    ring
  simp only [hpoint,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,hs,hr,hi,mul_one]
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring
