-- Prove2me | solution 1 for EdenVerified.p19_singularValueFunction_evolution_at_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:29:47.612996+00:00
-- url     : https://prove2.me/submissions/b028de06-c47e-4ef5-8035-1cd4830768ca

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValueFunction_evolution_at_target


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ}
    (hc : 4 < c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap (targetDimension c) =
      Real.exp (-6 * volumeDefect t p) :=
  @Eden.singularValueFunction_evolution_at_target
end EdenVerified
