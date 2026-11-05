-- Prove2me | solution 1 for GaussianSynthesis.centerColumn_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/b9d12d93-3f2f-447c-b217-da330b961171

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (x k : Int) : InCenterImage (centerColumn x k) := by
  simp only [InCenterImage, centerColumn, mixedCenterN]
  grind
end GaussianSynthesis
