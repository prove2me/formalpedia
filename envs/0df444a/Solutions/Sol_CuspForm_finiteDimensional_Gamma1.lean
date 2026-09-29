-- Prove2me | solution 1 for CuspForm.finiteDimensional_Gamma1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/142b491e-cf30-588f-8381-996dbdd8db21

import Mathlib
import Theorems.Thm_ModularForm_finiteDimensional_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_finiteDimensional_Gamma1

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (M : ℕ) [NeZero M] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) k) := by
  haveI := ModularForm.finiteDimensional_of_isArithmetic
    (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k
  exact FiniteDimensional.of_injective
    (CuspForm.toModularFormₗ : CuspForm (CongruenceSubgroup.Gamma1 M) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma1 M) k)
    CuspForm.toModularFormₗ_injective

end S_CuspForm_finiteDimensional_Gamma1
end P2MW
export P2MW.S_CuspForm_finiteDimensional_Gamma1 (solution)
