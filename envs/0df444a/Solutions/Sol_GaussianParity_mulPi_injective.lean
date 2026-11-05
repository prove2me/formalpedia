-- Prove2me | solution 1 for GaussianParity.mulPi_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/4507cc70-9c07-438f-8e7f-a4bf5130a8f1

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_GInt_ext

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution {u v : GInt} (h : mulPi u = mulPi v) : u = v := by
  apply GInt.ext
  · have hr := congrArg GInt.re h
    have hi := congrArg GInt.im h
    simp only [mulPi] at hr hi
    omega
  · have hr := congrArg GInt.re h
    have hi := congrArg GInt.im h
    simp only [mulPi] at hr hi
    omega
end GaussianParity
