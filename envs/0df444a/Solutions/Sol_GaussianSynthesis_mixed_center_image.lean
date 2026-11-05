-- Prove2me | solution 1 for GaussianSynthesis.mixed_center_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/ffe12748-2551-4452-92c9-02fe07694ad0

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (T sumInsideG sumOutsideG sumD sumB : Int)
    (hG : sumInsideG + sumOutsideG = 3*T)
    (hD : sumD = 19*T-sumInsideG)
    (hB : sumB = 2*sumOutsideG) :
    mixedCenterN sumB sumD = -32*T := by
  simp only [mixedCenterN]
  omega
end GaussianSynthesis
