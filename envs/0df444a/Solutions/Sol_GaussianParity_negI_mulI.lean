-- Prove2me | solution 1 for GaussianParity.negI_mulI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/1c969b94-70cc-4d75-bff8-48a61212eaa8

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (z : GInt) : negI (mulI z) = z := by
  apply GInt.ext <;> simp [mulI, negI]
end GaussianParity
