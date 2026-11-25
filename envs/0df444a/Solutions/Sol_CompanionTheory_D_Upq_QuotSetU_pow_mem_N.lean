-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.pow_mem_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:17.196113+00:00
-- url     : https://prove2.me/submissions/43c91210-d175-4ff1-808e-ea8e576e6d2e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_StabilizerModularFunctionTrivial
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_nilpotent_subgroup


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
theorem _root_.solution {x : 𝕄} (hx : x ∈ Nset k r) (p : ℕ) : x ^ p ∈ Nset k r := by
  induction p with
  | zero => rw [pow_zero]; exact (nilpotent_subgroup k r).1
  | succ p ih => rw [pow_succ]; exact (nilpotent_subgroup k r).2.1 _ ih _ hx
end CompanionTheory.D.Upq.QuotSetU
