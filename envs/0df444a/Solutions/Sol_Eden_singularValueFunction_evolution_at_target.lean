-- Prove2me | solution 1 for Eden.singularValueFunction_evolution_at_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:20.672445+00:00
-- url     : https://prove2.me/submissions/4901b238-fe6a-4ac9-9deb-008380c6283c

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
theorem _root_.solution {c t : ℝ}
    (hc : 4 < c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap (targetDimension c) =
      Real.exp (-6 * volumeDefect t p) := by
  have hd := targetDimension_bounds hc
  rw [singularValueFunction_evolution_on_four_five hc.le ht hp hd.1.le hd.2.le]
  congr 1
  unfold targetDimension
  have hcn : c ≠ 0 := by linarith
  field_simp
  ring
end Eden
