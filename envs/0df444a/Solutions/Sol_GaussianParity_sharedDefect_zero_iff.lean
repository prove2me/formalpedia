-- Prove2me | solution 1 for GaussianParity.sharedDefect_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/1e08c846-8156-452a-8f62-2df21a7616e7

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) :
    sharedDefect u v = 0 ↔ SameResidue u v := by
  simp only [sharedDefect, SameResidue, residue]
  omega
end GaussianParity
