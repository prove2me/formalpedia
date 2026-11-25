-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stabilizer_fourth_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:22:32.758544+00:00
-- url     : https://prove2.me/submissions/52b734c0-3766-4220-9bb8-a217585d3ba8

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.C1iv := by
  intro k r z z' γ hstd hpos
  have hγ : IsUnit γ.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hpos.1
  have hS : ∀ {w : Fin (2 * r + k + 1) → ℂ} {s : B.Mat k r}, s ∈ Sset k r w → IsUnit s.det := by
    rintro w s ⟨h, hh, m, hm, rfl⟩
    rw [Matrix.det_mul]
    exact (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1).mul (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hm.1)
  have key : ∀ a : B.Mat k r, IsUnit a.det → a⁻¹ * γ * (γ⁻¹ * a * γ) = γ := by
    intro a ha
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hγ,
      Matrix.nonsing_inv_mul_cancel_left _ _ ha]
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨ha, hb, he⟩
    have h1 : γ * b = a * γ := by
      have := congrArg (a * ·) he
      simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hS ha)] using this
    have hb' : b = γ⁻¹ * a * γ := by
      have := congrArg (γ⁻¹ * ·) h1
      simpa [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hγ] using this
    refine ⟨a, ⟨ha, b, hb, ?_⟩, rfl, hb'.symm⟩
    rw [hb']
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hγ, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hγ]
  · rintro ⟨g, hgH, rfl, rfl⟩
    obtain ⟨hg, s', hs', hgs⟩ := hgH
    refine ⟨hg, ?_, key g (hS hg)⟩
    have hb : γ⁻¹ * g * γ = s' := by
      rw [hgs]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγ, Matrix.mul_one,
        Matrix.nonsing_inv_mul_cancel_left _ _ hγ]
    rw [hb]
    exact hs'
end Formalism.FourierDecayAlt.P
