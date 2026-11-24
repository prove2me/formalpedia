-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagGramRestriction.Hst_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:49:42.759804+00:00
-- url     : https://prove2.me/submissions/531511d0-7a80-46b6-83d1-9f1487dacc20

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction

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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagGramRestriction
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} {γ : B.Mat k r} (hγ : IsUnit γ.det) (h : B.Mat k r) :
    h ∈ C2.Hst k r z z' γ ↔ h ∈ Sset k r z ∧ γ⁻¹ * h * γ ∈ Sset k r z' := by
  constructor
  · rintro ⟨hs, s', hs', rfl⟩
    refine ⟨hs, ?_⟩
    have : γ⁻¹ * (γ * s' * γ⁻¹) * γ = s' := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hγ, Matrix.nonsing_inv_mul _ hγ, Matrix.mul_one]
    rw [this]; exact hs'
  · rintro ⟨hs, hs'⟩
    refine ⟨hs, _, hs', ?_⟩
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hγ, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hγ]
end Formalism.FourierDecayAlt.P.FlagGramRestriction
