-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.pow_mem_UW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:13:08.159594+00:00
-- url     : https://prove2.me/submissions/2f38bcd1-964c-43b8-b934-b917cd6b393c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_StabilizerModularFunctionTrivial
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_mem_UW
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_one_mem_UW


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
theorem _root_.solution {x : 𝕄} (hx : x ∈ UWset k r z) (p : ℕ) : x ^ p ∈ UWset k r z := by
  induction p with
  | zero => rw [pow_zero]; exact one_mem_UW
  | succ p ih => rw [pow_succ]; exact mul_mem_UW ih hx
end CompanionTheory.D.Upq.QuotSetU
