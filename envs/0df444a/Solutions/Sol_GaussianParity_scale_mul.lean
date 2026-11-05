-- Prove2me | solution 1 for GaussianParity.scale_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/820eee95-a26e-42d4-93e5-5de280ad2216

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (k l : Int) (z : GInt) : scale k (scale l z) = scale (k*l) z := by
  apply GInt.ext <;> simp [scale, Int.mul_assoc]
end GaussianParity
