-- Prove2me | solution 1 for GaussianParity.residue_mulPi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/4d154ef6-1153-4623-92f6-7033dcebe528

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (z : GInt) : residue (mulPi z) = 0 := by
  simp only [residue, mulPi]
  omega
end GaussianParity
