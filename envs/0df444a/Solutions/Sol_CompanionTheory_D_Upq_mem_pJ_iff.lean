-- Prove2me | solution 1 for CompanionTheory.D.Upq.mem_pJ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:13:25.644288+00:00
-- url     : https://prove2.me/submissions/9604c570-7152-4985-9529-3629478d15b0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
import Theorems.Thm_CompanionTheory_D_Upq_mem_lieJ_iff
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
variable (J : Matrix n n ℂ)
variable {J} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ
namespace CompanionTheory.D.Upq
theorem _root_.solution {X : Matrix n n ℂ} : X ∈ pJ J ↔ X ∈ lieJ J ∧ Xᴴ = X := by
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · rw [(mem_lieJ_iff hJ).1 h.1, Matrix.mul_assoc J X J, h.2, Matrix.mul_neg, neg_neg,
      ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  · have e := J_mul_mul_J_of_mem hJ h.1
    rw [h.2] at e
    calc X * J = J * (J * X * J) := by
          rw [← Matrix.mul_assoc J (J * X) J, ← Matrix.mul_assoc J J X, hJ, Matrix.one_mul]
      _ = -(J * X) := by rw [e, Matrix.mul_neg]
end CompanionTheory.D.Upq
