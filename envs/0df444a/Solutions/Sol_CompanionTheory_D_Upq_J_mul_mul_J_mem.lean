-- Prove2me | solution 1 for CompanionTheory.D.Upq.J_mul_mul_J_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:19.168358+00:00
-- url     : https://prove2.me/submissions/bbfecfa8-6f89-46e8-b15f-900fb1ffd39a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
import Theorems.Thm_CompanionTheory_D_Upq_conjTranspose_mem_lieJ
import Theorems.Thm_CompanionTheory_D_Upq_J_mul_mul_J_of_mem

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
variable {J : Matrix n n ℂ} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ
namespace CompanionTheory.D.Upq
theorem _root_.solution {X : Matrix n n ℂ} (hX : X ∈ lieJ J) : J * X * J ∈ lieJ J := by
  rw [J_mul_mul_J_of_mem hJ hX]
  exact neg_mem (conjTranspose_mem_lieJ hJ hX)
end CompanionTheory.D.Upq
