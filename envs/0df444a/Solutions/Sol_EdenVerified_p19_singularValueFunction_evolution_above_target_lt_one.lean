-- Prove2me | solution 1 for EdenVerified.p19_singularValueFunction_evolution_above_target_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:29:49.196024+00:00
-- url     : https://prove2.me/submissions/8d2a7d4e-d481-43d3-9615-b844adfdafca

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValueFunction_evolution_above_target_lt_one


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t d : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd : targetDimension c < d) (hd₅ : d ≤ 5),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d < 1 :=
  @Eden.singularValueFunction_evolution_above_target_lt_one
end EdenVerified
