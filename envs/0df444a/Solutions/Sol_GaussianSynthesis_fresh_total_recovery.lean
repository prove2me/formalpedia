-- Prove2me | solution 1 for GaussianSynthesis.fresh_total_recovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/444bfb71-1013-4d86-aeff-dbbd5ec401a0

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_mixed_center_image

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (T sumInsideG sumOutsideG sumD sumB : Int)
    (hG : sumInsideG + sumOutsideG = 3*T)
    (hD : sumD = 19*T-sumInsideG)
    (hB : sumB = 2*sumOutsideG) :
    mixedCenterN sumB sumD / (-32) = T := by
  rw [mixed_center_image T sumInsideG sumOutsideG sumD sumB hG hD hB]
  omega
end GaussianSynthesis
