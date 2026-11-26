-- Prove2me | solution 1 for Eden.finiteTimeDimension_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:19.573664+00:00
-- url     : https://prove2.me/submissions/9ef8deb0-4fc8-4cd7-b39c-cf982f529892

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
import Theorems.Thm_Eden_finiteTimeDimension_eq_asymptotic_on_periodic
import Theorems.Thm_Eden_asymptoticDimension_at_origin
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_periodicEquilibriumSet_eq_positiveReturnSet
attribute [local simp] Eden.evolution_origin



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    finiteTimeDimension c t 0 = 0 := by
  have hp : (0 : PhaseSpace) ∈ periodicEquilibriumSet c := by
    rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)]
    exact ⟨1, by norm_num, evolution_origin c 1⟩
  rw [finiteTimeDimension_eq_asymptotic_on_periodic (by linarith) ht hp,
    asymptoticDimension_at_origin hc]
end Eden
