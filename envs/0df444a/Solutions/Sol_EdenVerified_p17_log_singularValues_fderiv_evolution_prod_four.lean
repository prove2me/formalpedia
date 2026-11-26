-- Prove2me | solution 1 for EdenVerified.p17_log_singularValues_fderiv_evolution_prod_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:27:49.402256+00:00
-- url     : https://prove2.me/submissions/cc80f0f5-a3c3-4114-afc9-7533ee75d15c

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_log_singularValues_fderiv_evolution_prod_four


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
    Real.log (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      4 * t - 6 * volumeDefect t p :=
  @Eden.log_singularValues_fderiv_evolution_prod_four
end EdenVerified
