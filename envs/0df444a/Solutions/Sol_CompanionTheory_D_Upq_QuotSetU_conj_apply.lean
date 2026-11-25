-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:46:12.109967+00:00
-- url     : https://prove2.me/submissions/8ec3fc65-d543-43c4-afb2-1fa78e36040f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract

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
theorem _root_.solution (t : ℝ) (g : 𝕄) (i j : Fin (2 * r + k + 1)) :
    (cdiag k r t * g * cdiag k r t⁻¹) i j = dvec t i * g i j * dvec t⁻¹ j := by
  rw [cdiag, cdiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
end CompanionTheory.D.Upq.QuotSetU
