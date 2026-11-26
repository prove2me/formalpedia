-- Prove2me | solution 1 for EdenVerified.p18_singularValues_fderiv_evolution_prod_four_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:28:34.41625+00:00
-- url     : https://prove2.me/submissions/7fa0aba3-a070-452e-b845-1510a7df0bff

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValues_fderiv_evolution_prod_four_le


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor),
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ≤
      Real.exp (4 * t) :=
  @Eden.singularValues_fderiv_evolution_prod_four_le
end EdenVerified
