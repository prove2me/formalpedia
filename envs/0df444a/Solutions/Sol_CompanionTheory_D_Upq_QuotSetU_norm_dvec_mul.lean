-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.norm_dvec_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:26.199484+00:00
-- url     : https://prove2.me/submissions/eb03457c-3af3-4fc3-8a64-c58154be989e

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
variable {z : Fin (2 * r + k + 1) → ℂ}
namespace CompanionTheory.D.Upq.QuotSetU
theorem _root_.solution (t : ℝ) (ht : 0 < t) (x : ℂ) (i j : Fin (2 * r + k + 1)) :
    ‖dvec (k := k) (r := r) t i * x * dvec t⁻¹ j‖ = t ^ (expo k r i - expo k r j) * ‖x‖ := by
  rw [dvec, dvec, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (zpow_pos ht _), abs_of_pos (zpow_pos (inv_pos.2 ht) _),
    _root_.inv_zpow', sub_eq_add_neg, zpow_add₀ ht.ne']
  ring
end CompanionTheory.D.Upq.QuotSetU
