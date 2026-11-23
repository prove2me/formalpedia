-- Prove2me | solution 1 for CompanionTheory.D.Upq.imG_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:55.219794+00:00
-- url     : https://prove2.me/submissions/c158db48-adb3-4430-bfae-b36bf0843718

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
import Theorems.Thm_CompanionTheory_D_Upq_thetaG_sub
import Theorems.Thm_CompanionTheory_D_Upq_thetaG_smul
import Theorems.Thm_CompanionTheory_D_Upq_thetaG_thetaG
import Theorems.Thm_CompanionTheory_D_Upq_mem_lieJ_iff_thetaG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (J : Matrix n n ℂ)
variable {J}
variable (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ hJh
namespace CompanionTheory.D.Upq
theorem _root_.solution (M : Matrix n n ℂ) : imG J M ∈ lieJ J := by
  rw [mem_lieJ_iff_thetaG hJ, imG, thetaG_smul, thetaG_sub, thetaG_thetaG hJ hJh,
    ← neg_sub M (thetaG J M), smul_neg, ← neg_smul]
  congr 1
  simp <;> ring
end CompanionTheory.D.Upq
