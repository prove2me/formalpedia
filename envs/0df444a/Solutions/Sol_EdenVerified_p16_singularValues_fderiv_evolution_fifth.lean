-- Prove2me | solution 1 for EdenVerified.p16_singularValues_fderiv_evolution_fifth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:27:06.677013+00:00
-- url     : https://prove2.me/submissions/4ff10bd8-53ae-44b6-8ade-65a7461df55c

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValues_fderiv_evolution_fifth


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    (fderiv ℝ (evolution c t) p).toLinearMap.singularValues 4 = Real.exp (-c * t) :=
  @Eden.singularValues_fderiv_evolution_fifth
end EdenVerified
