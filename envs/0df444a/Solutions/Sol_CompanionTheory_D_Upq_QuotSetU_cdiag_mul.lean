-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.cdiag_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:06.660595+00:00
-- url     : https://prove2.me/submissions/b4b55560-0161-430f-a757-ceaf7c1f1e30

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_dvec_mul_inv

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
theorem _root_.solution {t : ℝ} (ht : t ≠ 0) : cdiag k r t * cdiag k r t⁻¹ = 1 := by
  rw [cdiag, cdiag, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; exact dvec_mul_inv ht i
end CompanionTheory.D.Upq.QuotSetU
