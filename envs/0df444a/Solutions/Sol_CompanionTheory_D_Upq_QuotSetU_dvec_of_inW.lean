-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.dvec_of_inW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:12:45.656302+00:00
-- url     : https://prove2.me/submissions/91470b12-fb19-4d94-af8d-032cbd352bca

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_expo_eq_zero_of_inW

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
theorem _root_.solution {t : ℝ} {i : Fin (2 * r + k + 1)} (hi : inW k r i) : dvec (k := k) (r := r) t i = 1 := by
  rw [dvec, expo_eq_zero_of_inW hi, zpow_zero, Complex.ofReal_one]
end CompanionTheory.D.Upq.QuotSetU
