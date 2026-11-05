-- Prove2me | solution 1 for GaussianParity.dividePi_mulPi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/9336fbef-52a4-4c04-9e69-3d8d334779c5

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_GInt_ext

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (z : GInt) : dividePi (mulPi z) = z := by
  apply GInt.ext <;> simp only [dividePi, mulPi] <;> omega
end GaussianParity
