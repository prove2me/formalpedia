-- Prove2me | solution 1 for GaussianParity.gaussianMul_pi_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/0f900c6c-ed14-4778-9300-b8e7526260ad

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) :
    gaussianMul (mulPi u) (mulPi v) = scale 2 (mulI (gaussianMul u v)) := by
  apply GInt.ext <;> simp only [gaussianMul, mulPi, scale, mulI] <;> grind
end GaussianParity
