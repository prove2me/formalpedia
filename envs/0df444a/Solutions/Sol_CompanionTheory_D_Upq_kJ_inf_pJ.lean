-- Prove2me | solution 1 for CompanionTheory.D.Upq.kJ_inf_pJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:13.452289+00:00
-- url     : https://prove2.me/submissions/3cdf486b-601b-4215-95f9-2b56ba660973

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
import Theorems.Thm_CompanionTheory_D_Upq_J_J_mul

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
variable {J} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ
namespace CompanionTheory.D.Upq
theorem _root_.solution : kJ J ⊓ pJ J = ⊥ := by
  rw [eq_bot_iff]
  rintro X ⟨hK, hP⟩
  rw [Submodule.mem_bot]
  have h1 : J * X = -(J * X) := hK.2.symm.trans hP.2
  have h2 : J * X = 0 := by
    have : (2 : ℂ) • (J * X) = 0 := by rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel _
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  rw [← J_J_mul hJ X, h2, Matrix.mul_zero]
end CompanionTheory.D.Upq
