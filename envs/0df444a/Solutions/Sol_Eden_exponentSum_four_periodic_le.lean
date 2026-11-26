-- Prove2me | solution 1 for Eden.exponentSum_four_periodic_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:29.658007+00:00
-- url     : https://prove2.me/submissions/181c5593-3a22-49b6-9628-5ce9dea4ddb9

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
import Theorems.Thm_Eden_exponentSum_four_unit_circle
import Theorems.Thm_Eden_exponentSum_four_outer_circle
import Theorems.Thm_Eden_exponentSum_four_origin
import Theorems.Thm_Eden_mem_positiveReturnSet_iff
import Theorems.Thm_Eden_periodicEquilibriumSet_eq_positiveReturnSet


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ periodicEquilibriumSet c) : spectrumPartialSum (lyapunovExponent c p) 4 ≤ -2 := by
  rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)] at hp
  rcases (mem_positiveReturnSet_iff (by linarith) p).mp hp with rfl | h | h | h | h
  · rw [exponentSum_four_origin hc]; norm_num
  · exact (exponentSum_four_unit_circle hc (Or.inl h)).le
  · rw [exponentSum_four_outer_circle hc (Or.inl h)]; norm_num
  · exact (exponentSum_four_unit_circle hc (Or.inr h)).le
  · rw [exponentSum_four_outer_circle hc (Or.inr h)]; norm_num
end Eden
