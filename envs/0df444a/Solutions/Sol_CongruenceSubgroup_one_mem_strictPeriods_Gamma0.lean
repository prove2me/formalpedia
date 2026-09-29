-- Prove2me | solution 1 for CongruenceSubgroup.one_mem_strictPeriods_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/92a02cbc-2583-5f49-b340-9ac317890855

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (N : ℕ) : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)).strictPeriods := by
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  have h := Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT
  rw [h]
  exact AddSubgroup.mem_zmultiples (1 : ℝ)

end S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
end P2MW
export P2MW.S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0 (solution)
