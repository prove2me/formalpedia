-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.entry_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:12:48.612812+00:00
-- url     : https://prove2.me/submissions/13136543-ed5a-4981-a142-f7d256bfa815

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_StabilizerModularFunctionTrivial

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
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
namespace CompanionTheory.D.Upq.QuotSetU
theorem _root_.solution {g : 𝕄} (hg : ∀ i j, ‖(g - 1) i j‖ ≤ 1) (i j : Fin (2 * r + k + 1)) :
    ‖g i j‖ ≤ 2 := by
  have e : g i j = (g - 1) i j + (1 : 𝕄) i j := by
    rw [Matrix.sub_apply, sub_add_cancel]
  have h1 : ‖(1 : 𝕄) i j‖ ≤ 1 := by rw [Matrix.one_apply]; split_ifs <;> simp
  calc ‖g i j‖ = ‖(g - 1) i j + (1 : 𝕄) i j‖ := by rw [← e]
    _ ≤ ‖(g - 1) i j‖ + ‖(1 : 𝕄) i j‖ := norm_add_le _ _
    _ ≤ 2 := by linarith [hg i j]
end CompanionTheory.D.Upq.QuotSetU
