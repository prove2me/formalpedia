-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.expo_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:12:52.893044+00:00
-- url     : https://prove2.me/submissions/ff8fe52a-b784-4c48-8baf-6932070ce9e2

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
theorem _root_.solution {i j : Fin (2 * r + k + 1)} (hij : i.val < j.val) (hW : ¬ (inW k r i ∧ inW k r j)) :
    expo k r j + 1 ≤ expo k r i := by
  unfold expo; unfold inW at hW; split_ifs <;> omega
end CompanionTheory.D.Upq.QuotSetU
