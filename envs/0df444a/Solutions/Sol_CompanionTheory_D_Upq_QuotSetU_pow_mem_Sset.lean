-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.pow_mem_Sset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:08.088108+00:00
-- url     : https://prove2.me/submissions/45617a8f-21ef-469b-b3b9-3551295a2f96

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_StabilizerModularFunctionTrivial
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_mul_mem_Sset
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
namespace CompanionTheory.D.Upq.QuotSetU
theorem _root_.solution {x : 𝕄} (hx : x ∈ Sset k r z) (p : ℕ) : x ^ p ∈ Sset k r z := by
  induction p with
  | zero => rw [pow_zero]; exact one_mem_Sset
  | succ p ih => rw [pow_succ]; exact mul_mem_Sset ih hx
end CompanionTheory.D.Upq.QuotSetU
