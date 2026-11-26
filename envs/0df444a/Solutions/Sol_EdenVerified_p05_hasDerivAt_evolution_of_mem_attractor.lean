-- Prove2me | solution 1 for EdenVerified.p05_hasDerivAt_evolution_of_mem_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:10:12.768145+00:00
-- url     : https://prove2.me/submissions/48f9dcbb-0502-497d-9b55-6bde9db0f8c8

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_hasDerivAt_evolution_of_mem_attractor


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c t : ℝ) {p : PhaseSpace}
    (hp : p ∈ attractor),
    HasDerivAt (fun τ => evolution c τ p) (vectorField c (evolution c t p)) t :=
  @Eden.hasDerivAt_evolution_of_mem_attractor
end EdenVerified
