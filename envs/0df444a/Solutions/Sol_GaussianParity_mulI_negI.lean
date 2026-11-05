-- Prove2me | solution 1 for GaussianParity.mulI_negI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/ba733a0a-35e0-4382-9d4a-3c96e60b0f0e

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (z : GInt) : mulI (negI z) = z := by
  apply GInt.ext <;> simp [mulI, negI]
end GaussianParity
