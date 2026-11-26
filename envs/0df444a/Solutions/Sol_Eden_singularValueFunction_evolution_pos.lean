-- Prove2me | solution 1 for Eden.singularValueFunction_evolution_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:33.229417+00:00
-- url     : https://prove2.me/submissions/d4d94e87-f497-49c9-a888-3949e644d6ae

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Theorems.Thm_Eden_singularValues_evolution_pos


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (d : ℝ) :
    0 < singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d := by
  unfold singularValueFunction spectralProduct
  rw [← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos
    (singularValues_evolution_pos c ht p i) _)
end Eden
