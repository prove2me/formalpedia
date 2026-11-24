-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.TTw_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:58.848482+00:00
-- url     : https://prove2.me/submissions/1b64dd75-d89c-43a6-9d9e-8018baa00586

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf_positive_word_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf_negative_word_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf_transfer_word_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_liftMatrix_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_transpose_mul_of_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transpose_mul_of_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (QQ : K → M2 A) (w : List (Letter K S)) (hn : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup)
    (Y : K) : (TTw QQ w Y)ᵀ = (Xp w Y)ᵀ * lift0 (QQ Y)ᵀ * (Xm w Y)ᵀ := by
  induction w with
  | nil => simp [TTw, Xm, Xp, liftMatrix_transpose]
  | cons l w ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    by_cases h : l.plus
    · rw [show TTw QQ (l :: w) Y = TTw QQ w Y * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) from by simp [TTw, h],
        show (Xp (l :: w) Y : M2 (SlopeTestRemainingChoices S A)) = Xp w Y * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) from by simp [Xp, h],
        show (Xm (l :: w) Y : M2 (SlopeTestRemainingChoices S A)) = Xm w Y from by simp [Xm, h]]
      rw [transpose_mul_of_comm, transpose_mul_of_comm, ih hn.2]
      · simp only [mul_assoc]
      · intro i j k m
        have h1 : (Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) : M2 (SlopeTestRemainingChoices S A)) k m =
          (Y - l.pt - 1)⁻¹ • ((Y - l.pt) • (1 : M2 (SlopeTestRemainingChoices S A)) k m - eU l.intersection_update_fsHerm_neg_one m k) := rfl
        rw [h1]
        refine Commute.smul_right (Commute.sub_right (Commute.smul_right ?_ _)
          (freeOf_positive_word_matrix w hn.1 Y i j m k).symm) _
        rw [Matrix.one_apply]
        split_ifs
        · exact Commute.one_right _
        · exact Commute.zero_right _
      · intro i j k m
        have h1 : (Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) : M2 (SlopeTestRemainingChoices S A)) k m =
          (Y - l.pt - 1)⁻¹ • ((Y - l.pt) • (1 : M2 (SlopeTestRemainingChoices S A)) k m - eU l.intersection_update_fsHerm_neg_one m k) := rfl
        rw [h1]
        refine Commute.smul_right (Commute.sub_right (Commute.smul_right ?_ _)
          (freeOf_transfer_word_matrix QQ w hn.1 Y i j m k).symm) _
        rw [Matrix.one_apply]
        split_ifs
        · exact Commute.one_right _
        · exact Commute.zero_right _
    · rw [show TTw QQ (l :: w) Y = Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * TTw QQ w Y from by simp [TTw, h],
        show (Xp (l :: w) Y : M2 (SlopeTestRemainingChoices S A)) = Xp w Y from by simp [Xp, h],
        show (Xm (l :: w) Y : M2 (SlopeTestRemainingChoices S A)) = Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * Xm w Y from by simp [Xm, h]]
      rw [transpose_mul_of_comm, transpose_mul_of_comm, ih hn.2]
      · simp only [mul_assoc]
      · intro i j k m
        have h1 : (Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) : M2 (SlopeTestRemainingChoices S A)) i j =
          (l.pt - Y - 1)⁻¹ • ((l.pt - Y) • (1 : M2 (SlopeTestRemainingChoices S A)) i j - eU l.intersection_update_fsHerm_neg_one i j) := rfl
        rw [h1]
        refine Commute.smul_left (Commute.sub_left (Commute.smul_left ?_ _)
          (freeOf_negative_word_matrix w hn.1 Y k m i j)) _
        rw [Matrix.one_apply]
        split_ifs
        · exact Commute.one_left _
        · exact Commute.zero_left _
      · intro i j k m
        have h1 : (Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) : M2 (SlopeTestRemainingChoices S A)) i j =
          (l.pt - Y - 1)⁻¹ • ((l.pt - Y) • (1 : M2 (SlopeTestRemainingChoices S A)) i j - eU l.intersection_update_fsHerm_neg_one i j) := rfl
        rw [h1]
        refine Commute.smul_left (Commute.sub_left (Commute.smul_left ?_ _)
          (freeOf_transfer_word_matrix QQ w hn.1 Y k m i j)) _
        rw [Matrix.one_apply]
        split_ifs
        · exact Commute.one_left _
        · exact Commute.zero_left _
end Formalism.FourierDecayAlt.P.Wd7
