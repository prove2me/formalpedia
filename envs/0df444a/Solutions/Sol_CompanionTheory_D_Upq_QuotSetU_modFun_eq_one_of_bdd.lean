-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.modFun_eq_one_of_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:53:15.102909+00:00
-- url     : https://prove2.me/submissions/c7a1c564-4a60-4b83-8561-25785db139a7

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_StabilizerModularFunctionTrivial
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_modFun_one
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_modFun_pow
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_inv_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_pow_bdd_le_one
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_siegel_set_subset


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
variable {D : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ}
  (hD : UnitaryGroupMassFormula.ModProps (Sset k r z) D)
include hD
namespace CompanionTheory.D.Upq.QuotSetU
theorem _root_.solution {x : 𝕄} (hx : x ∈ Sset k r z) (hxi : x⁻¹ ∈ Sset k r z)
    (hb : ∃ M : ℝ, ∀ p : ℕ, D (x ^ p) ≤ M) (hbi : ∃ M : ℝ, ∀ p : ℕ, D (x⁻¹ ^ p) ≤ M) :
    D x = 1 := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨M', hM'⟩ := hbi
  have h1 : D x ≤ 1 := pow_bdd_le_one (hD.1 x hx) fun p => by rw [← modFun_pow hD hx]; exact hM p
  have h2 : D x⁻¹ ≤ 1 :=
    pow_bdd_le_one (hD.1 _ hxi) fun p => by rw [← modFun_pow hD hxi]; exact hM' p
  have h3 : D x * D x⁻¹ = 1 := by
    rw [← hD.2.1 x hx _ hxi, mul_inv_UH (siegel_set_subset k r z hx), modFun_one hD]
  have h4 := hD.1 x hx
  have h5 := hD.1 _ hxi
  nlinarith
end CompanionTheory.D.Upq.QuotSetU
