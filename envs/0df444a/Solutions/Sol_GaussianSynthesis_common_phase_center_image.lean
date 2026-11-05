-- Prove2me | solution 1 for GaussianSynthesis.common_phase_center_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/70e653b9-32d8-4457-ad96-1993f308a3ac

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_phase_scale

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (q : Nat) (N T : GInt)
    (h : N = scale (-32) T) :
    repeatI q N = scale (-32) (repeatI q T) := by
  rw [h,phase_scale]
end GaussianSynthesis
