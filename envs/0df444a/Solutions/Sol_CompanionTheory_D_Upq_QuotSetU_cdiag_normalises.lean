-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.cdiag_normalises
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:07:00.421847+00:00
-- url     : https://prove2.me/submissions/af2e9c36-6bce-4439-9190-2b0a91922722

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Theorems.Thm_P2M_CompanionTheory_D_Upq_QuotSetU_cdiag_mul__260c206f0917
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_inv
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_conj_S

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
variable {z : Fin (2 * r + k + 1) → ℂ}
namespace CompanionTheory.D.Upq.QuotSetU
theorem _root_.solution {t : ℝ} (ht : t ≠ 0) (g : 𝕄) :
    cdiag k r t * g * (cdiag k r t)⁻¹ ∈ Sset k r z ↔ g ∈ Sset k r z := by
  rw [cdiag_inv ht]
  refine ⟨fun h => ?_, cdiag_conj_S ht⟩
  have := cdiag_conj_S (z := z) (inv_ne_zero ht) h
  rwa [inv_inv, show cdiag k r t⁻¹ * (cdiag k r t * g * cdiag k r t⁻¹) * cdiag k r t =
      (cdiag k r t⁻¹ * cdiag k r t) * g * (cdiag k r t⁻¹ * cdiag k r t) by
        simp only [Matrix.mul_assoc], cdiag_mul' ht, Matrix.one_mul, Matrix.mul_one] at this
end CompanionTheory.D.Upq.QuotSetU
