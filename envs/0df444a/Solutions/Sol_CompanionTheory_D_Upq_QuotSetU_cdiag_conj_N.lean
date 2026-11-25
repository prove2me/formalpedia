-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.cdiag_conj_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:48:18.32136+00:00
-- url     : https://prove2.me/submissions/af179fe2-0805-41c3-92e9-19f2b0d776db

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_dvec_mul_inv
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_conj_apply
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_mem_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mem_Nset_iff
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_mem_UH


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
theorem _root_.solution {t : ℝ} (ht : t ≠ 0) {m : 𝕄} (hm : m ∈ Nset k r) :
    cdiag k r t * m * cdiag k r t⁻¹ ∈ Nset k r := by
  rw [mem_Nset_iff] at hm ⊢
  refine ⟨mul_mem_UH (mul_mem_UH (cdiag_mem_UH ht) hm.1) (cdiag_mem_UH (inv_ne_zero ht)),
    fun i j hj hi => ?_⟩
  rw [conj_apply, hm.2 i j hj hi]
  split_ifs with h
  · subst h; rw [mul_one, dvec_mul_inv ht]
  · rw [mul_zero, zero_mul]
end CompanionTheory.D.Upq.QuotSetU
