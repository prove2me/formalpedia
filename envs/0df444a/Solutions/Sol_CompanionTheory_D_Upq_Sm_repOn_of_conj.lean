-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.repOn_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:01:26.216801+00:00
-- url     : https://prove2.me/submissions/2f9b3362-4d98-48ac-82a3-b52ca2ec6c09

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Theorems.Thm_CCRuleCW_UH_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI.PhMeasCore
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution {J Hm P : Mat n} {σ : Mat n → (H →L[ℂ] H)} (hP : IsUnit P)
    (hPJ : Pᴴ * J * P = Hm) (h1 : σ (P⁻¹ * 1 * P) = 1)
    (hm : ∀ a, aᴴ * J * a = J → ∀ b, bᴴ * J * b = J →
      σ (P⁻¹ * (a * b) * P) = (σ (P⁻¹ * a * P)).comp (σ (P⁻¹ * b * P))) :
    RepOn {g | gᴴ * Hm * g = Hm} σ := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).mp hP
  have e1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have e3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, e2, conjTranspose_one]
  have hc : ∀ a : Mat n, P⁻¹ * (P * a * P⁻¹) * P = a := fun a => by
    rw [show P⁻¹ * (P * a * P⁻¹) * P = (P⁻¹ * P) * a * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      e1, Matrix.one_mul, Matrix.mul_one]
  have hJ : ∀ a : Mat n, aᴴ * Hm * a = Hm → (P * a * P⁻¹)ᴴ * J * (P * a * P⁻¹) = J := by
    intro a ha
    calc (P * a * P⁻¹)ᴴ * J * (P * a * P⁻¹) = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * J * P) * a) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = ((P⁻¹)ᴴ * Pᴴ) * J * (P * P⁻¹) := by
          rw [hPJ, ha, ← hPJ]; simp only [Matrix.mul_assoc]
      _ = J := by rw [e3, e2, Matrix.one_mul, Matrix.mul_one]
  refine ⟨by simp, fun a ha b hb => CCRuleCW.UH_mul Hm a b ha hb, ?_, fun a ha b hb => ?_⟩
  · rwa [Matrix.mul_one, e1] at h1
  · have := hm _ (hJ a ha) _ (hJ b hb)
    rw [hc, hc] at this
    rw [← this]
    congr 1
    rw [show P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) by
      simp only [Matrix.mul_assoc], e1]
    simp
end CompanionTheory.D.Upq.Sm
