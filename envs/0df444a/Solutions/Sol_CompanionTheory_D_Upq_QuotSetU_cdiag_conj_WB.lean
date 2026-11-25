-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.cdiag_conj_WB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:48:20.618584+00:00
-- url     : https://prove2.me/submissions/cea9b3d5-2054-416a-8f27-91355dd47cc1

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_dvec_mul_inv
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_dvec_of_inW
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_conj_apply

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
theorem _root_.solution {t : ℝ} (ht : t ≠ 0) {a : 𝕄} (ha : WB k r a) :
    cdiag k r t * a * cdiag k r t⁻¹ = a := by
  ext i j
  rw [conj_apply]
  by_cases hij : inW k r i ∧ inW k r j
  · rw [dvec_of_inW hij.1, dvec_of_inW hij.2, one_mul, mul_one]
  · rw [ha i j hij]
    split_ifs with h
    · subst h; rw [mul_one, dvec_mul_inv ht]
    · rw [mul_zero, zero_mul]
end CompanionTheory.D.Upq.QuotSetU
