-- Prove2me | solution 1 for EdenVerified.p10_hasDerivWithinAt_planarMovingPerturbation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:14:07.241381+00:00
-- url     : https://prove2.me/submissions/cea2b42f-d0e0-4610-ac16-900d054cc06f

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_hasDerivWithinAt_planarMovingPerturbation


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p v : PlanarSpace),
    HasDerivWithinAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) (Set.Ici 0) t :=
  @Eden.hasDerivWithinAt_planarMovingPerturbation
end EdenVerified
