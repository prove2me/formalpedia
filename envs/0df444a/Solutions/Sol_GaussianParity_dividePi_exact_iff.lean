-- Prove2me | solution 1 for GaussianParity.dividePi_exact_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/cec44863-fe21-4d0e-ba71-7c63df406d48

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_GInt_ext

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (z : GInt) : mulPi (dividePi z) = z ↔ PiDvd z := by
  constructor
  · intro h
    have hr := congrArg GInt.re h
    have hi := congrArg GInt.im h
    simp only [mulPi, dividePi] at hr hi
    simp only [PiDvd]
    omega
  · intro h
    apply GInt.ext
    · simp only [mulPi, dividePi, PiDvd] at *
      omega
    · simp only [mulPi, dividePi, PiDvd] at *
      omega
end GaussianParity
