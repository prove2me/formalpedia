-- Prove2me | solution 1 for EdenVerified.p16_evolution_mem_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:26:07.299693+00:00
-- url     : https://prove2.me/submissions/8d6d626e-22c0-4474-8394-c86af03d53eb

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_evolution_mem_attractor


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    evolution c t p ∈ attractor :=
  @Eden.evolution_mem_attractor
end EdenVerified
