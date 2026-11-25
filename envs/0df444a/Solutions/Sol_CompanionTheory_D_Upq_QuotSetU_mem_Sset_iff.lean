-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.mem_Sset_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:56:38.846354+00:00
-- url     : https://prove2.me/submissions/ad8ec69b-e95a-4327-8b4e-9296e0b3d2ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mul_UH__f897c67e29e4
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_inv_UH


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
theorem _root_.solution (g : 𝕄) : g ∈ Sset k r z ↔ ∃ h ∈ UWset k r z, h⁻¹ * g ∈ Nset k r := by
  constructor
  · rintro ⟨h, hh, m, hm, rfl⟩
    refine ⟨h, hh, ?_⟩
    rw [← Matrix.mul_assoc, inv_mul_UH' hh.1, Matrix.one_mul]
    exact hm
  · rintro ⟨h, hh, hm⟩
    refine ⟨h, hh, h⁻¹ * g, hm, ?_⟩
    rw [← Matrix.mul_assoc, mul_inv_UH hh.1, Matrix.one_mul]
end CompanionTheory.D.Upq.QuotSetU
