-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.cdiag_conj_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:24:22.009196+00:00
-- url     : https://prove2.me/submissions/7dd7a22a-4fc4-4a9b-abd9-1b9608bf2444

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Theorems.Thm_P2M_CompanionTheory_D_Upq_QuotSetU_cdiag_mul__260c206f0917
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_conj_WB
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_conj_N
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_wb_of_mem_UW


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
theorem _root_.solution {t : ℝ} (ht : t ≠ 0) {g : 𝕄} (hg : g ∈ Sset k r z) :
    cdiag k r t * g * cdiag k r t⁻¹ ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hg
  refine ⟨h, hh, cdiag k r t * m * cdiag k r t⁻¹, cdiag_conj_N ht hm, ?_⟩
  calc cdiag k r t * (h * m) * cdiag k r t⁻¹
      = (cdiag k r t * h * cdiag k r t⁻¹) * (cdiag k r t * m * cdiag k r t⁻¹) := by
        rw [show (cdiag k r t * h * cdiag k r t⁻¹) * (cdiag k r t * m * cdiag k r t⁻¹) =
          cdiag k r t * h * (cdiag k r t⁻¹ * cdiag k r t) * m * cdiag k r t⁻¹ by
            simp only [Matrix.mul_assoc], cdiag_mul' ht, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = h * (cdiag k r t * m * cdiag k r t⁻¹) := by rw [cdiag_conj_WB ht (wb_of_mem_UW hh)]
end CompanionTheory.D.Upq.QuotSetU
