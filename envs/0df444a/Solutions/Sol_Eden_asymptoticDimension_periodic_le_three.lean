-- Prove2me | solution 1 for Eden.asymptoticDimension_periodic_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:21.972083+00:00
-- url     : https://prove2.me/submissions/3ab8a8ba-18e5-4919-a774-26f443baac83

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
import Theorems.Thm_Eden_asymptoticDimension_at_origin
import Theorems.Thm_Eden_asymptoticDimension_first_unit_circle
import Theorems.Thm_Eden_asymptoticDimension_second_unit_circle
import Theorems.Thm_Eden_asymptoticDimension_first_outer_circle
import Theorems.Thm_Eden_asymptoticDimension_second_outer_circle
import Theorems.Thm_Eden_mem_positiveReturnSet_iff
import Theorems.Thm_Eden_periodicEquilibriumSet_eq_positiveReturnSet


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ periodicEquilibriumSet c) : asymptoticDimension c p ≤ 3 := by
  rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)] at hp
  rcases (mem_positiveReturnSet_iff (by linarith) p).mp hp with rfl | h | h | h | h
  · rw [asymptoticDimension_at_origin hc]; norm_num
  · exact (asymptoticDimension_first_unit_circle hc h).le
  · rw [asymptoticDimension_first_outer_circle hc h]; norm_num
  · exact (asymptoticDimension_second_unit_circle hc h).le
  · rw [asymptoticDimension_second_outer_circle hc h]; norm_num
end Eden
