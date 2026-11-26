-- Prove2me | solution 1 for EdenVerified.p05_evolution_mem_attractor_all_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:10:21.077974+00:00
-- url     : https://prove2.me/submissions/5af03352-f9e0-49c8-8f7c-096f21188687

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_evolution_mem_attractor_all_time


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c t : ℝ) {p : PhaseSpace} (hp : p ∈ attractor),
    evolution c t p ∈ attractor :=
  @Eden.evolution_mem_attractor_all_time
end EdenVerified
