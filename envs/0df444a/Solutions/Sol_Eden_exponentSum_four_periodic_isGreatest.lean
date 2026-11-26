-- Prove2me | solution 1 for Eden.exponentSum_four_periodic_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:44:55.754855+00:00
-- url     : https://prove2.me/submissions/0411b418-a8f6-4543-b00a-8b37d8756bf9

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
import Theorems.Thm_Eden_exponentSum_four_unit_circle
import Theorems.Thm_Eden_exponentSum_four_periodic_le
import Theorems.Thm_Eden_firstCircle_nonempty
import Theorems.Thm_Eden_mem_positiveReturnSet_iff
import Theorems.Thm_Eden_periodicEquilibriumSet_eq_positiveReturnSet


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 4) ''
      periodicEquilibriumSet c) (-2) := by
  constructor
  · obtain ⟨p, hp⟩ := firstCircle_nonempty (show (0 : ℝ) ≤ 1 by norm_num)
    refine ⟨p, ?_, exponentSum_four_unit_circle hc (Or.inl hp)⟩
    rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)]
    exact (mem_positiveReturnSet_iff (by linarith) p).mpr (Or.inr (Or.inl hp))
  · rintro x ⟨p, hp, rfl⟩
    exact exponentSum_four_periodic_le hc hp
end Eden
