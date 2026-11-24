-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.conj_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:01:25.225862+00:00
-- url     : https://prove2.me/submissions/79c1fe32-b2e1-446d-82d0-0c2b918f0d25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc

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
open PI.UpqRep
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution {n : ℕ} {J Hm P : Mat n} (hP : IsUnit P) (hPJ : Pᴴ * J * P = Hm) :
    (∀ a : Mat n, aᴴ * Hm * a = Hm → ∃ b : Mat n, bᴴ * J * b = J ∧ P⁻¹ * b * P = a) ∧
      ∀ b : Mat n, bᴴ * J * b = J → (P⁻¹ * b * P)ᴴ * Hm * (P⁻¹ * b * P) = Hm := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).mp hP
  have e1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have e3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, e2, conjTranspose_one]
  refine ⟨fun a ha => ⟨P * a * P⁻¹, ?_, ?_⟩, fun b hb => ?_⟩
  · calc (P * a * P⁻¹)ᴴ * J * (P * a * P⁻¹) = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * J * P) * a) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = ((P⁻¹)ᴴ * Pᴴ) * J * (P * P⁻¹) := by
          rw [hPJ, ha, ← hPJ]; simp only [Matrix.mul_assoc]
      _ = J := by rw [e3, e2, Matrix.one_mul, Matrix.mul_one]
  · rw [show P⁻¹ * (P * a * P⁻¹) * P = (P⁻¹ * P) * a * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      e1, Matrix.one_mul, Matrix.mul_one]
  · calc (P⁻¹ * b * P)ᴴ * Hm * (P⁻¹ * b * P)
        = Pᴴ * (bᴴ * (((P⁻¹)ᴴ * Pᴴ) * J * (P * P⁻¹)) * b) * P := by
          rw [← hPJ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Hm := by rw [e3, e2, Matrix.one_mul, Matrix.mul_one, hb, hPJ]
end CompanionTheory.D.Upq.Sm
