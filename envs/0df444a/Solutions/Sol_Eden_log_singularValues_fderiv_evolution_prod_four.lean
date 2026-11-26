-- Prove2me | solution 1 for Eden.log_singularValues_fderiv_evolution_prod_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:12:28.715862+00:00
-- url     : https://prove2.me/submissions/8273e560-90ba-49d5-8d79-9186e0e1cd68

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences
import Theorems.Thm_Eden_singularValues_fderiv_evolution_prod_four


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    Real.log (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      4 * t - 6 * volumeDefect t p := by
  rw [singularValues_fderiv_evolution_prod_four hc ht hp, Real.log_exp]
end Eden
