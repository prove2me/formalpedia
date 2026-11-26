-- Prove2me | solution 1 for Eden.hasDerivAt_planarMovingPerturbation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:12:41.642138+00:00
-- url     : https://prove2.me/submissions/2d157b65-7a4c-4707-92b9-c10ec53779f7

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_PlanarMovingFrame
import Theorems.Thm_Eden_hasDerivWithinAt_planarMovingPerturbation

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 < t)
    (p v : PlanarSpace) :
    HasDerivAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) t :=
  (hasDerivWithinAt_planarMovingPerturbation Ω ht.le p v).hasDerivAt (Ici_mem_nhds ht)
end Eden
