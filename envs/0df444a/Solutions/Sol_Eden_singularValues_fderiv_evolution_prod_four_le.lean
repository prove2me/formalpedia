-- Prove2me | solution 1 for Eden.singularValues_fderiv_evolution_prod_four_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:06:18.776283+00:00
-- url     : https://prove2.me/submissions/d27c5c76-e8c9-4180-aa2b-bf72dd56263a

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
import Theorems.Thm_Eden_volumeDefect_nonneg
import Theorems.Thm_Eden_singularValues_fderiv_evolution_prod_four

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ≤
      Real.exp (4 * t) := by
  rw [singularValues_fderiv_evolution_prod_four hc ht hp]
  exact Real.exp_le_exp.mpr (by linarith [volumeDefect_nonneg ht p])
end Eden
