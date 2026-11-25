-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.site_step_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:09:55.209662+00:00
-- url     : https://prove2.me/submissions/78fab1c7-617d-4c59-92e1-add44fe9f875

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_ins_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_ins_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_insert_mul_diagScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_insert_diagScalar_mul_of_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_TTw_factor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf_transfer_word_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_RRw
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_good_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_lift_reduction_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_liftMatrix_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_commute_Avr_Bvr_of_commute_siteOps
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_comm_Tstar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mem_ops_hol
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mem_ops_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_comm_bT
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_bT
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_comm_RRw
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_liftMatrix_commute_diagScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_TTw_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_QQ_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_commute_Avr_Bvr_of_commute_siteOps
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_comm


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
theorem _root_.solution
    (hE1 : ExchangePlusFactor) (hE2 : ExchangeMinusFactorStar) (hE3 : ExchangeMinusFactorTranspose) (hE4 : ExchangePlusFactorTranspose)
    (σ : Site A) (QQ QQ' : K → M2 A) (w : List (Letter K S))
    (hσ : IsSite σ) (hQ : QQCommutes QQ σ)
    (hrec : ∀ Y, star Y = Y → QQ' Y = (Ts σ Y)ᴴ * QQ Y * Ts σ Y) (hw : Good w) :
    star (bT σ w) * RRw QQ w * bT σ w = RRw QQ' w := by
  induction w with
  | nil => simp [bT, RRw]
  | cons l w ih =>
    obtain ⟨hg, hs, hre, -⟩ := good_cons hw
    have ih := ih hg
    have e1 := hE1 K A S σ w l.pt hσ hg
    have e2 := hE2 K A S σ w l.pt hσ hg hre
    have e3 := hE3 K A S σ w l.pt hσ hg hre
    have e4 := hE4 K A S σ w l.pt hσ hg
    have hfb : FreeOf l.intersection_update_fsHerm_neg_one (bT σ w) := free_bT σ w hs
    have hfR : FreeOf l.intersection_update_fsHerm_neg_one (RRw QQ w) := free_RRw QQ w hs
    have hQB : (lift0 (QQ l.pt) : M2 (SlopeTestRemainingChoices S A)) * d0 (bT σ w) = d0 (bT σ w) * lift0 (QQ l.pt) :=
      liftMatrix_commute_diagScalar _ _ fun i j => comm_bT σ w _ (hQ l.pt i j)
    have hQBt : (lift0 (QQ l.pt)ᵀ : M2 (SlopeTestRemainingChoices S A)) * d0 (bT σ w) = d0 (bT σ w) * lift0 (QQ l.pt)ᵀ :=
      liftMatrix_commute_diagScalar _ _ fun i j => comm_bT σ w _ (hQ l.pt j i)
    by_cases h : l.plus
    · have hb : bT σ (l :: w) = ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) * bT σ w := by simp [bT, vlet, h]
      have hR : RRw QQ (l :: w) = RRw QQ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt) := by simp [RRw, h]
      have hR' : RRw QQ' (l :: w) = RRw QQ' w * ins l.intersection_update_fsHerm_neg_one (TTw QQ' w l.pt) := by simp [RRw, h]
      have hst : star (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) : SlopeTestRemainingChoices S A) = ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ) := by
        rw [ins_star _ _ (freeOf2_lift _ _), liftMatrix_conjTranspose]
      have hcomm : Commute (RRw QQ w) (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ)) := by
        refine ins_comm _ _ _ hfR fun i j => ?_
        refine (comm_RRw QQ w _ fun Y i' j' => ?_).symm
        exact (comm_Tstar σ l.pt _ (fun x hx => hQ Y i' j' _ (mem_ops_star hx)) j i).symm
      have hM : (lift0 (Ts σ l.pt)ᴴ : M2 (SlopeTestRemainingChoices S A)) * TTw QQ w l.pt * lift0 (Ts σ l.pt) * d0 (bT σ w) =
          d0 (bT σ w) * TTw QQ' w l.pt := by
        rw [TTw_factor, TTw_factor, hrec l.pt hre, lift_reduction_mul, lift_reduction_mul]
        calc (lift0 (Ts σ l.pt)ᴴ : M2 (SlopeTestRemainingChoices S A)) * (Xm w l.pt * lift0 (QQ l.pt) * Xp w l.pt) *
              lift0 (Ts σ l.pt) * d0 (bT σ w)
            = lift0 (Ts σ l.pt)ᴴ * Xm w l.pt * lift0 (QQ l.pt) *
                (Xp w l.pt * lift0 (Ts σ l.pt) * d0 (bT σ w)) := by simp only [mul_assoc]
          _ = lift0 (Ts σ l.pt)ᴴ * Xm w l.pt * (lift0 (QQ l.pt) * d0 (bT σ w)) *
                lift0 (Ts σ l.pt) * Xp w l.pt := by rw [e1]; simp only [mul_assoc]
          _ = (lift0 (Ts σ l.pt)ᴴ * Xm w l.pt * d0 (bT σ w)) * lift0 (QQ l.pt) *
                lift0 (Ts σ l.pt) * Xp w l.pt := by rw [hQB]; simp only [mul_assoc]
          _ = d0 (bT σ w) * (Xm w l.pt * (lift0 (Ts σ l.pt)ᴴ * lift0 (QQ l.pt) * lift0 (Ts σ l.pt)) *
                Xp w l.pt) := by rw [e2]; simp only [mul_assoc]
      have hI : (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ) : SlopeTestRemainingChoices S A) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt) *
          ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) * bT σ w = bT σ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ' w l.pt) := by
        rw [← ins_mul _ _ _ (freeOf2_lift _ _),
          ← ins_mul _ _ _ (freeOf2_mul (freeOf2_lift _ _) (freeOf_transfer_word_matrix QQ w hs _)),
          ← insert_mul_diagScalar, hM, insert_diagScalar_mul_of_free _ _ _ hfb]
      rw [hb, hR, hR', star_mul, hst, ← ih]
      calc star (bT σ w) * ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ) * (RRw QQ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)) *
            (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) * bT σ w)
          = star (bT σ w) * (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ) * RRw QQ w) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt) *
            ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) * bT σ w := by simp only [mul_assoc]
        _ = star (bT σ w) * RRw QQ w * (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt) *
            ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) * bT σ w) := by rw [← hcomm.eq]; simp only [mul_assoc]
        _ = _ := by rw [hI]; simp only [mul_assoc]
    · have hb : bT σ (l :: w) = ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) * bT σ w := by
        simp [bT, vlet, h]
      have hR : RRw QQ (l :: w) = RRw QQ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)ᵀ := by simp [RRw, h]
      have hR' : RRw QQ' (l :: w) = RRw QQ' w * ins l.intersection_update_fsHerm_neg_one (TTw QQ' w l.pt)ᵀ := by simp [RRw, h]
      have hst : star (ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) : SlopeTestRemainingChoices S A) =
          ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ) := by
        rw [ins_star _ _ (freeOf2_lift _ _), liftMatrix_conjTranspose]
        congr 2
        ext i j
        simp
      have hcomm : Commute (RRw QQ w) (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ)) := by
        refine ins_comm _ _ _ hfR fun i j => ?_
        refine (comm_RRw QQ w _ fun Y i' j' => ?_).symm
        exact (commute_Avr_Bvr_of_commute_siteOps σ l.pt _ (fun x hx => hQ Y i' j' _ (mem_ops_hol hx)) j i).symm
      have hM : (lift0 (Ts σ l.pt)ᵀ : M2 (SlopeTestRemainingChoices S A)) * (TTw QQ w l.pt)ᵀ *
          lift0 ((Ts σ l.pt).map star) * d0 (bT σ w) = d0 (bT σ w) * (TTw QQ' w l.pt)ᵀ := by
        rw [TTw_transpose _ _ hg.1, TTw_transpose _ _ hg.1, hrec l.pt hre,
          QQ_transpose σ hσ _ _ (hQ l.pt), lift_reduction_mul, lift_reduction_mul]
        calc (lift0 (Ts σ l.pt)ᵀ : M2 (SlopeTestRemainingChoices S A)) *
              ((Xp w l.pt)ᵀ * lift0 (QQ l.pt)ᵀ * (Xm w l.pt)ᵀ) *
              lift0 ((Ts σ l.pt).map star) * d0 (bT σ w)
            = lift0 (Ts σ l.pt)ᵀ * (Xp w l.pt)ᵀ * lift0 (QQ l.pt)ᵀ *
                ((Xm w l.pt)ᵀ * lift0 ((Ts σ l.pt).map star) * d0 (bT σ w)) := by
              simp only [mul_assoc]
          _ = lift0 (Ts σ l.pt)ᵀ * (Xp w l.pt)ᵀ * (lift0 (QQ l.pt)ᵀ * d0 (bT σ w)) *
                lift0 ((Ts σ l.pt).map star) * (Xm w l.pt)ᵀ := by rw [e3]; simp only [mul_assoc]
          _ = (lift0 (Ts σ l.pt)ᵀ * (Xp w l.pt)ᵀ * d0 (bT σ w)) * lift0 (QQ l.pt)ᵀ *
                lift0 ((Ts σ l.pt).map star) * (Xm w l.pt)ᵀ := by rw [hQBt]; simp only [mul_assoc]
          _ = d0 (bT σ w) * ((Xp w l.pt)ᵀ * (lift0 (Ts σ l.pt)ᵀ * lift0 (QQ l.pt)ᵀ *
                lift0 ((Ts σ l.pt).map star)) * (Xm w l.pt)ᵀ) := by rw [e4]; simp only [mul_assoc]
      have hI : (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ) : SlopeTestRemainingChoices S A) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)ᵀ *
          ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) * bT σ w =
          bT σ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ' w l.pt)ᵀ := by
        rw [← ins_mul _ _ _ (freeOf2_lift _ _),
          ← ins_mul _ _ _ (freeOf2_mul (freeOf2_lift _ _) (freeOf2_transpose (freeOf_transfer_word_matrix QQ w hs _))),
          ← insert_mul_diagScalar, hM, insert_diagScalar_mul_of_free _ _ _ hfb]
      rw [hb, hR, hR', star_mul, hst, ← ih]
      calc star (bT σ w) * ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ) * (RRw QQ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)ᵀ) *
            (ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) * bT σ w)
          = star (bT σ w) * (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ) * RRw QQ w) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)ᵀ *
            ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) * bT σ w := by simp only [mul_assoc]
        _ = star (bT σ w) * RRw QQ w * (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)ᵀ *
            ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) * bT σ w) := by
              rw [← hcomm.eq]; simp only [mul_assoc]
        _ = _ := by rw [hI]; simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Wd7
