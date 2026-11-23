-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:43.842372+00:00
-- url     : https://prove2.me/submissions/6b2f5da3-26af-4cb2-93ec-dc1ef2b04b06

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {B : Type} [Ring B] [StarRing B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution (F Fi d τ τi τ' τi' l RR T00 T01 T10 T11 U10 U11 : B) (q : ℂ)
    (hRR : RR = star F * d * F) (hF : F * Fi = 1) (hF' : Fi * F = 1)
    (hdτ : star (d * τ) = d * τ) (hτ : τi * τ = 1) (hτ1 : τ' * τi' = 1) (hτ2 : τi' * τ' = 1)
    (h11 : F * T11 = τ * F) (h10 : F * T10 = τ * l * F) (hU : F * U11 = τ' * F)
    (herm : star (RR * T10) = RR * T01)
    (quantum_determinant_shifted : T00 * U11 - T01 * U10 = q • (1 : B)) (upper_block_det_one : T10 * U11 = T11 * U10) :
    RR * T11 = star F * (d * τ) * F ∧ RR * T10 = star F * (d * τ * l) * F ∧
      RR * T01 = star F * (star l * (d * τ)) * F ∧
      RR * T00 = star F * (q • (d * τi') + star l * (d * τ) * l) * F := by
  have hFl : ∀ X : B, X * F * Fi = X := fun X => by rw [mul_assoc, hF, mul_one]
  have h3l : ∀ X : B, X * τ' * τi' = X := fun X => by rw [mul_assoc, hτ1, mul_one]
  have hT11 : RR * T11 = star F * (d * τ) * F := by
    rw [hRR, mul_assoc (star F * d) F T11, h11]
    simp only [mul_assoc]
  have hT10 : RR * T10 = star F * (d * τ * l) * F := by
    rw [hRR, mul_assoc (star F * d) F T10, h10]
    simp only [mul_assoc]
  have hT01 : RR * T01 = star F * (star l * (d * τ)) * F := by
    rw [← herm, hT10, star_mul, star_mul, star_star, star_mul, hdτ]
    simp only [mul_assoc]
  have hU11 : U11 = Fi * τ' * F := by
    calc U11 = Fi * F * U11 := by rw [hF', one_mul]
      _ = Fi * τ' * F := by rw [mul_assoc Fi F U11, hU, ← mul_assoc]
  have hUi : U11 * (Fi * τi' * F) = 1 := by
    rw [hU11]
    simp only [← mul_assoc, hFl, h3l, hF']
  have hFU10 : F * U10 = l * F * U11 := by
    have e : τ * (F * U10) = τ * (l * F * U11) := by
      calc τ * (F * U10) = F * T11 * U10 := by rw [h11, mul_assoc]
        _ = F * T10 * U11 := by rw [mul_assoc F T11 U10, ← upper_block_det_one, ← mul_assoc]
        _ = τ * (l * F * U11) := by rw [h10]; simp only [mul_assoc]
    calc F * U10 = τi * τ * (F * U10) := by rw [hτ, one_mul]
      _ = τi * (τ * (l * F * U11)) := by rw [mul_assoc τi τ (F * U10), e]
      _ = l * F * U11 := by rw [← mul_assoc τi τ, hτ, one_mul]
  have e2 : T00 * U11 = q • (1 : B) + T01 * U10 := by rw [← quantum_determinant_shifted, sub_add_cancel]
  have hT00 : T00 = (q • (1 : B) + T01 * U10) * (Fi * τi' * F) := by
    calc T00 = T00 * (U11 * (Fi * τi' * F)) := by rw [hUi, mul_one]
      _ = (q • (1 : B) + T01 * U10) * (Fi * τi' * F) := by rw [← mul_assoc T00, e2]
  have hA : RR * (q • (1 : B)) * (Fi * τi' * F) = star F * (q • (d * τi')) * F := by
    rw [mul_smul_comm, mul_one, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, hRR]
    congr 1
    simp only [← mul_assoc, hFl]
  have hB : RR * (T01 * U10) * (Fi * τi' * F) = star F * (star l * (d * τ) * l) * F := by
    rw [← mul_assoc RR T01 U10, hT01, mul_assoc (star F * (star l * (d * τ))) F U10, hFU10,
      mul_assoc (star F * (star l * (d * τ))) (l * F * U11), mul_assoc (l * F) U11, hUi, mul_one]
    simp only [mul_assoc]
  refine ⟨hT11, hT10, hT01, ?_⟩
  rw [hT00, ← mul_assoc RR, mul_add, add_mul, hA, hB, mul_add, add_mul]
end Formalism.FourierDecayAlt.P.Fr5
