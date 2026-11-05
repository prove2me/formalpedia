-- Prove2me | solution 1 for GaussianSynthesis.phase_inverse_restores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/a84bc949-661b-4863-a74b-e1c38f11b3c0

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (x : Fraction) : phaseNegI (phaseI x) = x := by
  cases x
  simp only [phaseNegI, phaseI]
  congr
  apply GInt.ext <;> simp [mulNegI,mulI]
end GaussianSynthesis
