-- Prove2me | solution 1 for GaussianSynthesis.centerPlus_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/2bba2d09-7b7c-4675-a2b6-b7589f16bd1a

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (u v : CenterTotals)
    (hu : InCenterImage u) (hv : InCenterImage v) : InCenterImage (centerPlus u v) := by
  simp only [InCenterImage, centerPlus, mixedCenterN] at *
  omega
end GaussianSynthesis
