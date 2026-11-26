-- Prove2me | solution 1 for Eden.finiteTimeDimension_le_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:06:30.243177+00:00
-- url     : https://prove2.me/submissions/8decaa1f-04ec-44d8-9dbf-9419cf6aed95

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
import Theorems.Thm_Eden_singularValueFunction_evolution_above_target_lt_one
import Theorems.Thm_Eden_finiteTimeDimension_isGreatest


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) : finiteTimeDimension c t p ≤ targetDimension c := by
  have hmax := finiteTimeDimension_isGreatest c ht.le p
  by_contra h
  have hlt := singularValueFunction_evolution_above_target_lt_one hc ht hp
    (lt_of_not_ge h) hmax.1.1.2
  exact (not_lt_of_ge hmax.1.2) hlt
end Eden
