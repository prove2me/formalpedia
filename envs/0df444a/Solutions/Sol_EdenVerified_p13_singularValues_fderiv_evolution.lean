-- Prove2me | solution 1 for EdenVerified.p13_singularValues_fderiv_evolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:23:55.359088+00:00
-- url     : https://prove2.me/submissions/ae55d400-5835-40b2-802d-da551ddfecbd

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValues_fderiv_evolution


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Finset.univ.val.map (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) :=
  @Eden.singularValues_fderiv_evolution
end EdenVerified
