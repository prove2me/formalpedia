-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.cdiag_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:47:07.641703+00:00
-- url     : https://prove2.me/submissions/7933f504-4156-4edf-b3c2-c662d748c69e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_mul

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
variable {k r : ℕ}
local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
namespace CompanionTheory.D.Upq.QuotSetU
theorem _root_.solution {t : ℝ} (ht : t ≠ 0) : (cdiag k r t)⁻¹ = cdiag k r t⁻¹ :=
  Matrix.inv_eq_right_inv (cdiag_mul ht)
end CompanionTheory.D.Upq.QuotSetU
