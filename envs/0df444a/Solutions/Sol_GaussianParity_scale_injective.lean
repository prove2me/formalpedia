-- Prove2me | solution 1 for GaussianParity.scale_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/dae67774-6ff8-4ee7-b865-a51b88fb7a5a

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (k : Int) (hk : k ≠ 0) {u v : GInt}
    (h : scale k u = scale k v) : u = v := by
  apply GInt.ext
  · have hr := congrArg GInt.re h
    simp only [scale] at hr
    exact Int.eq_of_mul_eq_mul_left hk hr
  · have hi := congrArg GInt.im h
    simp only [scale] at hi
    exact Int.eq_of_mul_eq_mul_left hk hi
end GaussianParity
