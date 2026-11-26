-- Prove2me | solution 1 for EdenVerified.p19_singularValueFunction_evolution_above_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:29:48.194354+00:00
-- url     : https://prove2.me/submissions/74ea85eb-f214-4ba7-babe-e894fc3f4631

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValueFunction_evolution_above_target


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
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (-6 * volumeDefect t p - c * t * (d - targetDimension c)) :=
  @Eden.singularValueFunction_evolution_above_target
end EdenVerified
