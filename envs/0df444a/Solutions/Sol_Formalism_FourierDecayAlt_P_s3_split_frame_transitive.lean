-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.s3_split_frame_transitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:48:34.717972+00:00
-- url     : https://prove2.me/submissions/4f9d9e3f-4479-4210-bf4f-d07b6822a570

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_exists_equiv_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_exists_over
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_rank_eq_iff_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_surjective_of_rank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Module Formalism.FourierDecayAlt.P.S3x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.SplitFrameTransitive := by
  intro K _ _ n a X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hXY
  obtain ⟨g₀, hg₀⟩ := exists_equiv_comp _ _ ((rank_eq_iff_injective X₁).mp hX₁)
    ((rank_eq_iff_injective Y₁).mp hY₁)
  set G := LinearMap.toMatrix' g₀.toLinearMap with hG
  have hGl : Matrix.toLin' G = g₀.toLinearMap := by rw [hG, Matrix.toLin'_toMatrix']
  have hGdet : IsUnit G.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have : Matrix.toLin' G x = Matrix.toLin' G y := hxy
    rw [hGl] at this
    exact g₀.injective this
  have hGX : G * X₁ = Y₁ := by
    apply (Matrix.toLin' (R := K)).injective
    rw [Matrix.toLin'_mul, hGl]
    exact LinearMap.ext hg₀
  have hY₂' : (Gᵀ * Y₂).rank = a := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by rwa [Matrix.det_transpose]), hY₂]
  have hjj : X₁ᵀ * X₂ = X₁ᵀ * (Gᵀ * Y₂) := by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hGX]
    have := congrArg Matrix.transpose hXY
    simpa [Matrix.transpose_mul] using this
  obtain ⟨h, hinj, hπ, hh⟩ := exists_over (Matrix.toLin' X₁ᵀ) (surjective_of_rank X₁ hX₁)
    (Matrix.toLin' X₂) (Matrix.toLin' (Gᵀ * Y₂)) ((rank_eq_iff_injective X₂).mp hX₂)
    ((rank_eq_iff_injective _).mp hY₂') (by rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hjj])
  set H := LinearMap.toMatrix' h with hH
  have hHl : Matrix.toLin' H = h := by rw [hH, Matrix.toLin'_toMatrix']
  have hHdet : IsUnit H.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have : Matrix.toLin' H x = Matrix.toLin' H y := hxy
    rw [hHl] at this
    exact hinj this
  have h1 : X₁ᵀ * H = X₁ᵀ := by
    apply (Matrix.toLin' (R := K)).injective
    rw [Matrix.toLin'_mul, hHl, hπ]
  have h2 : H * (Gᵀ * Y₂) = X₂ := by
    apply (Matrix.toLin' (R := K)).injective
    rw [Matrix.toLin'_mul, hHl, hh]
  refine ⟨G * Hᵀ, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_transpose]
    exact hGdet.mul hHdet
  · have h3 : Hᵀ * X₁ = X₁ := by
      have := congrArg Matrix.transpose h1
      simpa [Matrix.transpose_mul] using this
    rw [Matrix.mul_assoc, h3, hGX]
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, h2]
end Formalism.FourierDecayAlt.P
