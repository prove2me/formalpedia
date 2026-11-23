-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.rank_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:41.667697+00:00
-- url     : https://prove2.me/submissions/bdeb3823-01ab-465e-a350-2d79c1bfce06

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [Fintype K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) (hX : X.rank = a)
    (J : Matrix (Fin n) (Fin n) K) (hdJ : IsUnit J.det) : (Xᴴ * J).rank = a := by
  have hsurj : Function.Surjective Xᵀ.mulVec := by
    have h1 : LinearMap.range Xᵀ.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      have := rank_transpose X
      rw [hX] at this
      exact this
    intro y
    have hy : y ∈ LinearMap.range Xᵀ.mulVecLin := by rw [h1]; trivial
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, by rw [← hx, Matrix.mulVecLin_apply]⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  have h2 : Rᵀ * X = 1 := by
    have := congrArg transpose hR
    simpa [transpose_mul] using this
  have h3 : Xᴴ * Rᵀᴴ = 1 := by
    have := congrArg conjTranspose h2
    simpa [conjTranspose_mul] using this
  have h4 : (Xᴴ * J) * (J⁻¹ * Rᵀᴴ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, mul_nonsing_inv _ hdJ, Matrix.one_mul, h3]
  apply le_antisymm
  · simpa using rank_le_card_height (Xᴴ * J)
  · have := rank_mul_le_left (Xᴴ * J) (J⁻¹ * Rᵀᴴ)
    rw [h4, rank_one, Fintype.card_fin] at this
    exact this
end Formalism.FourierDecayAlt.P.S3x5
