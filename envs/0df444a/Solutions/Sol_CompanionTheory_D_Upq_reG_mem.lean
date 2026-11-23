-- Prove2me | solution 1 for CompanionTheory.D.Upq.reG_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:13.633824+00:00
-- url     : https://prove2.me/submissions/6e0425c7-0a8c-429a-add9-3e5c6d1e6cea

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
import Theorems.Thm_CompanionTheory_D_Upq_thetaG_add
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
theorem _root_.solution (M : Matrix n n ℂ) : reG J M ∈ lieJ J := by
  rw [mem_lieJ_iff_thetaG hJ, reG, thetaG_smul, thetaG_add, thetaG_thetaG hJ hJh,
    add_comm (thetaG J M)]
  congr 1
  simp
end CompanionTheory.D.Upq
