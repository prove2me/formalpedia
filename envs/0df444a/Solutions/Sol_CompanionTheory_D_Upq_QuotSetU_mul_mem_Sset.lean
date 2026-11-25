-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.mul_mem_Sset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:32:24.847976+00:00
-- url     : https://prove2.me/submissions/1604ad76-fade-40d8-862f-462f04f7f25b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_wb_of_mem_UW
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_conj_mem_N
import Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mul_UH__f897c67e29e4
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mem_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mem_UW
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_inv_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_mem_UW
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_nilpotent_subgroup


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
theorem _root_.solution {a b : 𝕄} (ha : a ∈ Sset k r z) (hb : b ∈ Sset k r z) :
    a * b ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  obtain ⟨h', hh', m', hm', rfl⟩ := hb
  have hconj : h'⁻¹ * m * h' ∈ Nset k r :=
    conj_mem_N (wb_of_mem_UW (inv_mem_UW hh')) (wb_of_mem_UW hh') (inv_mul_UH' hh'.1)
      (inv_mem_UH hh'.1) hh'.1 hm
  refine ⟨h * h', mul_mem_UW hh hh', h'⁻¹ * m * h' * m', (nilpotent_subgroup k r).2.1 _ hconj _ hm', ?_⟩
  calc h * m * (h' * m') = h * (h' * h'⁻¹) * m * h' * m' := by
        rw [mul_inv_UH hh'.1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = h * h' * (h'⁻¹ * m * h' * m') := by simp only [Matrix.mul_assoc]
end CompanionTheory.D.Upq.QuotSetU
