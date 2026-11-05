-- Prove2me | solution 1 for GaussianParity.mulPi_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/a17569aa-2afb-4f2d-9084-91b9b7beaf4e

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (k : Int) (z : GInt) :
    mulPi (scale k z) = scale k (mulPi z) := by
  apply GInt.ext <;> simp [mulPi, scale] <;> grind
end GaussianParity
