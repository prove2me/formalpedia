-- Prove2me | solution 1 for Eden.asymptoticDimension_periodic_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:24.781658+00:00
-- url     : https://prove2.me/submissions/ef352f61-7aaa-4f53-9e57-4ebaa292670a

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
import Theorems.Thm_Eden_asymptoticDimension_first_unit_circle
import Theorems.Thm_Eden_asymptoticDimension_periodic_le_three
import Theorems.Thm_Eden_firstCircle_nonempty
import Theorems.Thm_Eden_mem_positiveReturnSet_iff
import Theorems.Thm_Eden_periodicEquilibriumSet_eq_positiveReturnSet


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    IsGreatest (asymptoticDimension c '' periodicEquilibriumSet c) 3 := by
  constructor
  · obtain ⟨p, hp⟩ := firstCircle_nonempty (show (0 : ℝ) ≤ 1 by norm_num)
    refine ⟨p, ?_, asymptoticDimension_first_unit_circle hc hp⟩
    rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)]
    exact (mem_positiveReturnSet_iff (by linarith) p).mpr (Or.inr (Or.inl hp))
  · rintro d ⟨p, hp, rfl⟩
    exact asymptoticDimension_periodic_le_three hc hp
end Eden
