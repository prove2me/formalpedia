-- Prove2me | solution 1 for GaussianParity.residue_mulI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/12fb9621-a8b1-4b7b-854d-1ba8c402997a

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (z : GInt) : residue (mulI z) = residue z := by
  simp only [residue, mulI]
  omega
end GaussianParity
