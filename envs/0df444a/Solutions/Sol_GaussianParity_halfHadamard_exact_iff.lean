-- Prove2me | solution 1 for GaussianParity.halfHadamard_exact_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/9267e4ab-7def-4682-ac43-5ec0ba80950f

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_GInt_ext

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) :
    (scaleTwo (halfHadamard u v).1 = add u v ∧
     scaleTwo (halfHadamard u v).2 = add u (neg v)) ↔
    (u.re % 2 = v.re % 2 ∧ u.im % 2 = v.im % 2) := by
  constructor
  · intro h
    have hr := congrArg GInt.re h.1
    have hi := congrArg GInt.im h.1
    simp only [scaleTwo, halfHadamard, add] at hr hi
    omega
  · intro h
    constructor <;> apply GInt.ext <;>
      simp only [scaleTwo, halfHadamard, add, neg] <;> omega
end GaussianParity
