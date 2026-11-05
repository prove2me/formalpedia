-- Prove2me | solution 1 for GaussianSynthesis.dirty_center_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/d3cd32cc-6f91-4ce2-b735-4381f5ff7413

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution :
    mixedCenterN 1 0 = 1 ∧ ¬ ∃ T : Int, mixedCenterN 1 0 = -32*T := by
  simp only [mixedCenterN]
  constructor
  · decide
  · omega
end GaussianSynthesis
