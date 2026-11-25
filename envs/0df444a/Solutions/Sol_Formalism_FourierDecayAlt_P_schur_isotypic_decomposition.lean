-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.schur_isotypic_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:51:08.474282+00:00
-- url     : https://prove2.me/submissions/795bf3dc-670a-4d95-a894-2b4f45f905a6

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TorusArgumentMultiplicative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate InnerProductSpace ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.SchurIsotypic := by
  intro K _ E E' R _ _ _ _ _ _ _ _ _ π π' ρ hπ hπ' _ hno J hJ φ hφ v x
  have unit : ∀ {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (σ : K →* (A →L[ℂ] A)),
      C7.IsUnitaryRep σ → ∀ k a b, ⟪σ k a, b⟫_ℂ = ⟪a, σ k⁻¹ b⟫_ℂ := by
    intro A _ _ σ hσ k a b
    have e : σ k (σ k⁻¹ b) = b := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
    conv_lhs => rw [← e]
    exact hσ k a (σ k⁻¹ b)
  let ψ : R →L[ℂ] E' := ContinuousLinearMap.adjoint J ∘L φ
  have hψ : C7.Intertw ρ π' ψ := by
    intro k
    ext y
    apply ext_inner_right ℂ
    intro z
    simp only [ψ, ContinuousLinearMap.comp_apply]
    rw [unit π' hπ', ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    have h1 := DFunLike.congr_fun (hJ k⁻¹) z
    have h2 := DFunLike.congr_fun (hφ k) y
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [← h1, ← unit π hπ, h2]
  have h0 := hno ψ hψ
  have : ⟪φ x, J v⟫_ℂ = ⟪ψ x, v⟫_ℂ := by
    simp only [ψ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  rw [this, h0]; simp
end Formalism.FourierDecayAlt.P
