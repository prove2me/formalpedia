-- Prove2me | solution 1 for GaussianSynthesis.rawC_left_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/9fe052f3-3f62-4535-9796-d7a61a2ed8ef

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (u v : GInt) :
    numeratorLeft (numeratorLeft u v) (numeratorRight u v) = mulPi (mulPi v) := by
  apply GInt.ext <;> simp only [numeratorLeft, numeratorRight, add, mulI, mulPi] <;> omega
end GaussianSynthesis
