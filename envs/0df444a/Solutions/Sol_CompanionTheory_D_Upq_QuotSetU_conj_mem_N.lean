-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.conj_mem_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:11:59.522056+00:00
-- url     : https://prove2.me/submissions/2e556af6-2fb9-4ab4-8559-96c19afb842b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_nc_conj
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
theorem _root_.solution {a b m : 𝕄} (ha : WB k r a) (hb : WB k r b) (hab : a * b = 1)
    (haU : a ∈ UH (Hpk k r)) (hbU : b ∈ UH (Hpk k r)) (hm : m ∈ Nset k r) :
    a * m * b ∈ Nset k r := by
  rw [mem_Nset_iff] at hm ⊢
  exact ⟨mul_mem_UH (mul_mem_UH haU hm.1) hbU, nc_conj ha hb hab hm.2⟩
end CompanionTheory.D.Upq.QuotSetU
