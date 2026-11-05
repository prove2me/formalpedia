-- Prove2me | solution 1 for GaussianSynthesis.fresh_doubled_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/4e6c06f7-d8e0-4e61-ba77-f6a8634a53de

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (G B : Int) (h : B = 2*G) : B/2 = G := by
  omega
end GaussianSynthesis
