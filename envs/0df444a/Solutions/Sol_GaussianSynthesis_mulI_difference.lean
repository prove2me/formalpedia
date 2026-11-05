-- Prove2me | solution 1 for GaussianSynthesis.mulI_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/605b2d21-a08b-4367-a6c7-8bded607a82c

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (u v : GInt) :
    mulI (gaussianDifference u v) = gaussianDifference (mulI u) (mulI v) := by
  apply GInt.ext <;> simp only [mulI,gaussianDifference,add,neg] <;> omega
end GaussianSynthesis
