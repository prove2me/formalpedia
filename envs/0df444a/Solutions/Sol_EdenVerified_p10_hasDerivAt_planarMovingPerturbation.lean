-- Prove2me | solution 1 for EdenVerified.p10_hasDerivAt_planarMovingPerturbation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:55.66408+00:00
-- url     : https://prove2.me/submissions/94d0fea2-c74a-4b2b-a40f-3dbe4f046596

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_hasDerivAt_planarMovingPerturbation


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 < t)
    (p v : PlanarSpace),
    HasDerivAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) t :=
  @Eden.hasDerivAt_planarMovingPerturbation
end EdenVerified
