-- Prove2me | solution 1 for GaussianParity.residue_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/368390b1-1ecd-41db-bad4-9f44702c023c

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) : residue (add u v) = (residue u + residue v) % 2 := by
  simp only [residue, add]
  omega
end GaussianParity
