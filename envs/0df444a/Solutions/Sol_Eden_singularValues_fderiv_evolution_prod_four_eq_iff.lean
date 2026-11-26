-- Prove2me | solution 1 for Eden.singularValues_fderiv_evolution_prod_four_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:06:23.096397+00:00
-- url     : https://prove2.me/submissions/ad59a467-8662-4ed4-af22-9deabafada93

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
import Theorems.Thm_Eden_volumeDefect_eq_zero_iff
import Theorems.Thm_Eden_singularValues_fderiv_evolution_prod_four

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor) :
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t) ↔ p ∈ torus := by
  rw [singularValues_fderiv_evolution_prod_four hc ht.le hp, Real.exp_eq_exp]
  rw [← volumeDefect_eq_zero_iff ht hp]
  constructor <;> intro h <;> linarith
end Eden
