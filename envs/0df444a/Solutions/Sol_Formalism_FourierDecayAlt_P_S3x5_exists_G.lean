-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.exists_G
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:50.681943+00:00
-- url     : https://prove2.me/submissions/e0a0d21c-e006-49d6-b112-44607cf3657e

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_exists_frame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (htr : ∃ μ : K, μ + star μ ≠ 0)
    (hnorm : ∀ t : K, t ≠ 0 → star t = t → ∃ l : K, star l * l = t)
    {μ ν : Type} [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
    (hcard : Fintype.card μ = Fintype.card ν) (J : Matrix μ μ K) (D : Matrix ν ν K)
    (hJ : Jᴴ = J) (hdJ : IsUnit J.det) (hD : Dᴴ = D) (hdD : IsUnit D.det) :
    ∃ (G : Matrix μ ν K) (G' : Matrix ν μ K), G * G' = 1 ∧ G' * G = 1 ∧ Gᴴ * J * G = D := by
  obtain ⟨X, hX⟩ := exists_frame htr hnorm J hJ hdJ (Fintype.card μ) le_rfl
  obtain ⟨Y, hY⟩ := exists_frame htr hnorm D hD hdD (Fintype.card μ) hcard.le
  have hX' : X * (Xᴴ * J) = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp)).1 hX
  have hY' : Y * (Yᴴ * D) = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hcard])).1 hY
  refine ⟨X * (Yᴴ * D), Y * (Xᴴ * J), ?_, ?_, ?_⟩
  · calc X * (Yᴴ * D) * (Y * (Xᴴ * J)) = X * (Yᴴ * D * Y) * (Xᴴ * J) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hY, Matrix.mul_one, hX']
  · calc Y * (Xᴴ * J) * (X * (Yᴴ * D)) = Y * (Xᴴ * J * X) * (Yᴴ * D) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hX, Matrix.mul_one, hY']
  · calc (X * (Yᴴ * D))ᴴ * J * (X * (Yᴴ * D)) = D * Y * (Xᴴ * J * X) * (Yᴴ * D) := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
      _ = D * (Y * (Yᴴ * D)) := by rw [hX, Matrix.mul_one, Matrix.mul_assoc]
      _ = D := by rw [hY', Matrix.mul_one]
end Formalism.FourierDecayAlt.P.S3x5
