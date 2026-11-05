-- Prove2me | solution 1 for GaussianParity.mulI_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/cd1a1245-2c32-4af2-bac9-e48968e960e7

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (k : Int) (z : GInt) : mulI (scale k z) = scale k (mulI z) := by
  apply GInt.ext <;> simp [mulI, scale] <;> grind
end GaussianParity
