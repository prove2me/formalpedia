-- Prove2me | solution 1 for GaussianParity.mulPi_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/9895c267-42f3-41af-9390-d285b427dc22

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (z : GInt) : mulPi (mulPi z) = scale 2 (mulI z) := by
  apply GInt.ext <;> simp [mulPi, mulI, scale] <;> omega
end GaussianParity
