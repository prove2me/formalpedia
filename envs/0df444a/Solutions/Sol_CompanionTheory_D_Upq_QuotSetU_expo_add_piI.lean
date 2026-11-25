-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.expo_add_piI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:21.780526+00:00
-- url     : https://prove2.me/submissions/5ee4a945-60a0-481b-bff2-d06f549fe935

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_val


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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : expo k r i + expo k r (piI k r i) = 0 := by
  have hp := piI_val (k := k) (r := r) i
  have := i.isLt
  unfold expo
  split_ifs at hp ⊢ <;> omega
end CompanionTheory.D.Upq.QuotSetU
