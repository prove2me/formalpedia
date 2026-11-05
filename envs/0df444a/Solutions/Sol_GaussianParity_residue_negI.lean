-- Prove2me | solution 1 for GaussianParity.residue_negI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/aeb7766c-4803-4262-b916-f4c556342995

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (z : GInt) : residue (negI z) = residue z := by
  simp only [residue, negI]
  omega
end GaussianParity
