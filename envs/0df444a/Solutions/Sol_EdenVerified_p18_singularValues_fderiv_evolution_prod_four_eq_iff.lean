-- Prove2me | solution 1 for EdenVerified.p18_singularValues_fderiv_evolution_prod_four_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:28:38.187514+00:00
-- url     : https://prove2.me/submissions/859271a2-0047-4519-a494-02babb454c97

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValues_fderiv_evolution_prod_four_eq_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor),
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t) ↔ p ∈ torus :=
  @Eden.singularValues_fderiv_evolution_prod_four_eq_iff
end EdenVerified
