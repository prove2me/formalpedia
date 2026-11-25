-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.modFun_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:58.419484+00:00
-- url     : https://prove2.me/submissions/049200b6-dd3e-4735-b4c3-f578aefae02a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_StabilizerModularFunctionTrivial
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_pow_mem_Sset
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_modFun_one

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
theorem _root_.solution {x : 𝕄} (hx : x ∈ Sset k r z) (p : ℕ) : D (x ^ p) = D x ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero]; exact modFun_one hD
  | succ p ih => rw [pow_succ, pow_succ, hD.2.1 _ (pow_mem_Sset hx p) _ hx, ih]
end CompanionTheory.D.Upq.QuotSetU
