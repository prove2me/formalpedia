-- Prove2me | solution 1 for GaussianSynthesis.matching_phase_dirty_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/2e363909-2554-4482-8179-1726ed522a0a

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_gaussian_update_difference
import Theorems.Thm_GaussianSynthesis_phase_difference

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (q : Nat) (old fresh : GInt) :
    gaussianDifference (repeatI q (add old fresh)) (repeatI q old) = repeatI q fresh := by
  rw [← phase_difference,gaussian_update_difference]
end GaussianSynthesis
