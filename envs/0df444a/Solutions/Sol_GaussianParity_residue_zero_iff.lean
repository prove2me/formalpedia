-- Prove2me | solution 1 for GaussianParity.residue_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/d08272e5-120c-481f-bfb3-e5813dca358b

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (z : GInt) : residue z = 0 ↔ PiDvd z := by
  simp only [residue, PiDvd]
  omega
end GaussianParity
