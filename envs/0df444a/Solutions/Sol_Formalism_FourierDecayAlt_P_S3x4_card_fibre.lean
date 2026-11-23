-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.card_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:27.342657+00:00
-- url     : https://prove2.me/submissions/9201458a-b36e-4167-8708-2b88dcb060c5

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_card_ker_inf
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_rank_eq_iff_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_surjective_of_rank
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_finrank_ker_of_rank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
variable {K : Type} [Field K]
namespace Formalism.FourierDecayAlt.P.S3x4
theorem _root_.solution [Fintype K] (n a : ℕ) (R : Matrix (Fin a) (Fin a) K)
    (X₁ : Matrix (Fin n) (Fin a) K) (hX : X₁.rank = a) :
    Nat.card {X₂ : Matrix (Fin n) (Fin a) K // X₂.rank = a ∧ X₂ᵀ * X₁ = Rᵀ} =
      Fintype.card K ^ ((n - a) * R.rank) *
        ∏ j ∈ range (a - R.rank), (Fintype.card K ^ (n - a) - Fintype.card K ^ j) := by
  obtain ⟨σ, hσ0⟩ := (Matrix.toLin' X₁ᵀ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (surjective_of_rank X₁ hX))
  have hσ : ∀ x, Matrix.toLin' X₁ᵀ (σ x) = x := fun x => by
    simpa using congrArg (fun φ => φ x) hσ0
  have e : {X₂ : Matrix (Fin n) (Fin a) K // X₂.rank = a ∧ X₂ᵀ * X₁ = Rᵀ} ≃
      {j : (Fin a → K) →ₗ[K] (Fin n → K) //
        Function.Injective j ∧ Matrix.toLin' X₁ᵀ ∘ₗ j = Matrix.toLin' R} :=
    (Matrix.toLin' (R := K) (m := Fin n) (n := Fin a)).toEquiv.subtypeEquiv
      (p := fun X₂ : Matrix (Fin n) (Fin a) K => X₂.rank = a ∧ X₂ᵀ * X₁ = Rᵀ)
      (q := fun j : (Fin a → K) →ₗ[K] (Fin n → K) =>
        Function.Injective j ∧ Matrix.toLin' X₁ᵀ ∘ₗ j = Matrix.toLin' R)
      (fun X₂ => by
        refine and_congr (rank_eq_iff_injective X₂) ?_
        show _ ↔ Matrix.toLin' X₁ᵀ ∘ₗ Matrix.toLin' X₂ = Matrix.toLin' R
        rw [← Matrix.toLin'_mul, (Matrix.toLin' (R := K)).injective.eq_iff,
          ← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.transpose_transpose])
  rw [Nat.card_congr e, Nat.card_congr (fibEquiv _ σ hσ _), card_ker_inf,
    finrank_ker_of_rank X₁ hX]
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' R)
  rw [Module.finrank_fin_fun] at h
  have h0 : R.rank = finrank K (LinearMap.range (Matrix.toLin' R)) := by
    rw [Matrix.rank, Matrix.toLin'_apply']
  rw [← h0] at h ⊢
  have h1 : finrank K (LinearMap.ker (Matrix.toLin' R)) = a - R.rank := by omega
  rw [h1]
end Formalism.FourierDecayAlt.P.S3x4
