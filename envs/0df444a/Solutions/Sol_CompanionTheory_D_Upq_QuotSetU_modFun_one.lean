-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.modFun_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:32:40.464514+00:00
-- url     : https://prove2.me/submissions/5534e43d-f0e0-44cd-8faa-a718725cdefd

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_StabilizerModularFunctionTrivial
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_one_mem_Sset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.QuotSetU
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
variable {D : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ}
  (hD : UnitaryGroupMassFormula.ModProps (Sset k r z) D)
include hD
namespace CompanionTheory.D.Upq.QuotSetU
theorem _root_.solution : D 1 = 1 := by
  have h := hD.2.1 1 one_mem_Sset 1 one_mem_Sset
  rw [Matrix.one_mul] at h
  have h0 := hD.1 1 one_mem_Sset
  have h' : D 1 * D 1 = D 1 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ h0.ne' h'
end CompanionTheory.D.Upq.QuotSetU
