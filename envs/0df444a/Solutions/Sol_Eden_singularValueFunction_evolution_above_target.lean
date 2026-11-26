-- Prove2me | solution 1 for Eden.singularValueFunction_evolution_above_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:21.928279+00:00
-- url     : https://prove2.me/submissions/97bf30c2-773f-4b94-bd35-ff02f01b91cc

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
import Theorems.Thm_Eden_singularValueFunction_evolution_on_four_five
import Theorems.Thm_Eden_targetDimension_bounds


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t d : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd : targetDimension c < d) (hd₅ : d ≤ 5) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (-6 * volumeDefect t p - c * t * (d - targetDimension c)) := by
  rw [singularValueFunction_evolution_on_four_five hc.le ht.le hp
    ((targetDimension_bounds hc).1.trans hd).le hd₅]
  congr 1
  unfold targetDimension
  have hcn : c ≠ 0 := by linarith
  field_simp
  ring
end Eden
