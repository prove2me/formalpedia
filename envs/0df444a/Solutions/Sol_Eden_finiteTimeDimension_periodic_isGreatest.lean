-- Prove2me | solution 1 for Eden.finiteTimeDimension_periodic_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:01.540943+00:00
-- url     : https://prove2.me/submissions/55c1f4ab-30e7-4c0a-97b2-3d867656e76f

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
import Theorems.Thm_Eden_asymptoticDimension_periodic_isGreatest
import Theorems.Thm_Eden_asymptoticDimension_periodic_le_three
import Theorems.Thm_Eden_finiteTimeDimension_eq_asymptotic_on_periodic


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    IsGreatest (finiteTimeDimension c t '' periodicEquilibriumSet c) 3 := by
  constructor
  · obtain ⟨p, hp, hdim⟩ := (asymptoticDimension_periodic_isGreatest hc).1
    exact ⟨p, hp, (finiteTimeDimension_eq_asymptotic_on_periodic (by linarith) ht hp).trans hdim⟩
  · rintro d ⟨p, hp, rfl⟩
    rw [finiteTimeDimension_eq_asymptotic_on_periodic (by linarith) ht hp]
    exact asymptoticDimension_periodic_le_three hc hp
end Eden
