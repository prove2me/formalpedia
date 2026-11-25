-- Prove2me | solution 1 for CompanionTheory.D.Upq.kJ_sup_pJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:16.4995+00:00
-- url     : https://prove2.me/submissions/cd0a352e-4628-44fd-b9c0-63c90e67fb85

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
import Theorems.Thm_CompanionTheory_D_Upq_mul_J_J
import Theorems.Thm_CompanionTheory_D_Upq_J_mul_mul_J_mem
import Theorems.Thm_CompanionTheory_D_Upq_kJ_le
import Theorems.Thm_CompanionTheory_D_Upq_pJ_le

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
theorem _root_.solution : kJ J ⊔ pJ J = lieJ J := by
  refine le_antisymm (sup_le (kJ_le J) (pJ_le J)) fun X hX => ?_
  have hX' := J_mul_mul_J_mem hJ hX
  refine Submodule.mem_sup.2 ⟨(1 / 2 : ℝ) • (X + J * X * J), ⟨Submodule.smul_mem _ _ (add_mem hX hX'), ?_⟩,
    (1 / 2 : ℝ) • (X - J * X * J), ⟨Submodule.smul_mem _ _ (sub_mem hX hX'), ?_⟩, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, mul_J_J hJ,
      ← Matrix.mul_assoc J (J * X) J, ← Matrix.mul_assoc J J X, hJ, Matrix.one_mul, add_comm (J * X)]
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, mul_J_J hJ,
      ← Matrix.mul_assoc J (J * X) J, ← Matrix.mul_assoc J J X, hJ, Matrix.one_mul, ← smul_neg, neg_sub]
  · rw [← smul_add, add_add_sub_cancel, ← two_smul ℝ X, smul_smul]
    norm_num
end CompanionTheory.D.Upq
