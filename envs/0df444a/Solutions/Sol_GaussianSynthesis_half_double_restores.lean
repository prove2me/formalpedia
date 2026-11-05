-- Prove2me | solution 1 for GaussianSynthesis.half_double_restores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/9567c1d9-b132-4bd0-b89b-1131a8de221d

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_two_pi_numerator_sameValue
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (x : Fraction) : SameValue (exactHalf (exactDouble x)) x := by
  have hp : mulI (scaleTwo x.numerator) = mulPi (mulPi x.numerator) := by
    apply GInt.ext <;> simp only [mulI,scaleTwo,mulPi] <;> omega
  simp only [exactHalf,exactDouble]
  rw [hp]
  exact two_pi_numerator_sameValue _ _
end GaussianSynthesis
