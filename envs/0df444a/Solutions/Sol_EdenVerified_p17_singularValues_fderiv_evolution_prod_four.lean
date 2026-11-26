-- Prove2me | solution 1 for EdenVerified.p17_singularValues_fderiv_evolution_prod_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:28:04.719289+00:00
-- url     : https://prove2.me/submissions/eb6a0d4b-46fd-49a8-a03e-ec52f0de59be

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValues_fderiv_evolution_prod_four


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
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t - 6 * volumeDefect t p) :=
  @Eden.singularValues_fderiv_evolution_prod_four
end EdenVerified
