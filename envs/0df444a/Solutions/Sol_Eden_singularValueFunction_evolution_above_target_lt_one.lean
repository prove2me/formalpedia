-- Prove2me | solution 1 for Eden.singularValueFunction_evolution_above_target_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:04:26.971783+00:00
-- url     : https://prove2.me/submissions/7ca1308c-e6ea-4ba6-97f1-b48e143f1e59

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
import Theorems.Thm_Eden_singularValueFunction_evolution_above_target
import Theorems.Thm_Eden_volumeDefect_nonneg


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t d : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd : targetDimension c < d) (hd₅ : d ≤ 5) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d < 1 := by
  rw [singularValueFunction_evolution_above_target hc ht hp hd hd₅, Real.exp_lt_one_iff]
  have hpos : 0 < c * t * (d - targetDimension c) :=
    mul_pos (mul_pos (by linarith) ht) (sub_pos.mpr hd)
  linarith [volumeDefect_nonneg ht.le p]
end Eden
