-- Prove2me | solution 1 for Eden.hasDerivAt_amplitudeSq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:51:58.56434+00:00
-- url     : https://prove2.me/submissions/03bf6286-6d30-46f8-960a-d27d6aa6c978

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
import Theorems.Thm_Eden_hasDerivAt_amplitudeSq_of_discriminant_pos
import Theorems.Thm_Eden_radialDiscriminant_pos


set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun τ => amplitudeSq τ s)
      (2 * q (squaredRadiusEvolution t s) * amplitudeSq t s) t :=
  hasDerivAt_amplitudeSq_of_discriminant_pos (radialDiscriminant_pos ht s)
end Eden
