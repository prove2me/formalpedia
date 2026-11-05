-- Prove2me | solution 1 for GaussianParity.component_parity_implies_sameResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/b5607a42-0fc0-44ce-8c77-ccf8c424fda0

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt)
    (hre : u.re % 2 = v.re % 2) (him : u.im % 2 = v.im % 2) : SameResidue u v := by
  simp only [SameResidue, residue]
  omega
end GaussianParity
