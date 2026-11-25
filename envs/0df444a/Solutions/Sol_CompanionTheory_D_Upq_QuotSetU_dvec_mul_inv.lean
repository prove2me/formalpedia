-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.dvec_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:46:08.873532+00:00
-- url     : https://prove2.me/submissions/5b285bf0-f46e-4ae6-ac07-ee34b03d5238

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
theorem _root_.solution {t : ℝ} (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) :
    dvec (k := k) (r := r) t i * dvec t⁻¹ i = 1 := by
  rw [dvec, dvec, ← Complex.ofReal_mul, ← mul_zpow, mul_inv_cancel₀ ht, _root_.one_zpow,
    Complex.ofReal_one]
end CompanionTheory.D.Upq.QuotSetU
