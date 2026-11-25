-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.wb_of_mem_UW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:30:01.617958+00:00
-- url     : https://prove2.me/submissions/d65605a5-b363-4f18-89b7-77102d4dc834

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_uw_block


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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {h : 𝕄} (hh : h ∈ UWset k r z) : WB k r h :=
  fun i j hij => uw_block hh i j hij
end CompanionTheory.D.Upq.QuotSetU
