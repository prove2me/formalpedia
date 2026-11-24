-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.dualityList_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:12.266264+00:00
-- url     : https://prove2.me/submissions/faa474b4-cac3-442d-9f51-3d913b831c2a

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_reg_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_freeOf_J_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_freeOf_matrix_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_diagScalar_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_Rht0_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_Rh0_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_ins_twine
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_twine_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_J_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_Jt_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_J_entry_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_good_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_reg_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_ph_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_Ps_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_diagScalar_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_diagScalar_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_J_matrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd10
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P.Wd10
theorem _root_.solution (hIF : InsFree) (hIS : InsStar) (hWF : WordFree) (hWM : WordModule)
    (hDP : DualPlus) (hDM : DualMinus) : DualityList := by
  intro K A S _ _ _ _ _ _ _ _ QQ q w L hSt
  induction L with
  | nil =>
    intro _ _ _
    refine ⟨isUnit_one, one_ne_zero, ?_, ?_, ?_⟩
    · simp [Ps, JL]
    · simp [Ps, kap]
    · intro Y _ _
      simp [Ps, ph, d0]
  | cons l L ih =>
    intro hG hGd hOK
    obtain ⟨hG', hnot, hstar, hregY⟩ := good_cons hG
    obtain ⟨hGd', -, -, hregd⟩ := good_cons hGd
    obtain ⟨hR1, hq, hOK'⟩ := hOK
    obtain ⟨hU', hk', h3', h4', h5'⟩ := ih hG' hGd' hOK'
    have hM := hWM K A S QQ q (L ++ w) hSt hG'
    obtain ⟨hfR, hfT⟩ := hWF K A S QQ (L ++ w) l.intersection_update_fsHerm_neg_one hnot
    have hfP : FreeOf l.intersection_update_fsHerm_neg_one (Ps QQ q w L) := Ps_free hIF hWF QQ q w l.intersection_update_fsHerm_neg_one L hnot
    have hph : ph L (dl l).pt ≠ 0 := ph_ne L _ (reg_left hR1) (reg_left hregd)
    have hkap : kap q w (l :: L) ≠ 0 := div_ne_zero (mul_ne_zero hk' hq) hph
    obtain ⟨p, a, Y⟩ := l
    cases p
    ·
      change Reg (L ++ w) (Y - 1) at hR1
      change qw q (L ++ w) (Y - 1) ≠ 0 at hq
      change Reg (L.map dl ++ w) (Y - 1) at hregd
      obtain ⟨m1, m2, m3, m4⟩ := hDM K A S {Y | Reg (L ++ w) Y} (RRw QQ (L ++ w)) (TTw QQ (L ++ w))
        (qw q (L ++ w)) a Y hM hfR hfT hregY hR1 hstar hq
      have ePs : Ps QQ q w (⟨false, a, Y⟩ :: L) =
          PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y * Ps QQ q w L := rfl
      have eRR : RRw QQ ((⟨false, a, Y⟩ :: L) ++ w) =
          RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)ᵀ := rfl
      have eRRd : RRw QQ ((⟨false, a, Y⟩ :: L).map dl ++ w) =
          RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y - 1)) := rfl
      have eJL : (JL (⟨false, a, Y⟩ :: L) : SlopeTestRemainingChoices S A) = ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ * JL L := rfl
      have ekap : kap q w (⟨false, a, Y⟩ :: L) = kap q w L * qw q (L ++ w) (Y - 1) / ph L (Y - 1) :=
        rfl
      have hcomm : Commute (star (Ps QQ q w L)) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ) := by
        have c0 : Commute (Ps QQ q w L) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) :=
          (hIF K A S a _).2 _ hfP (fun i j => J_entry_comm _ i j)
        have c1 : Commute (Ps QQ q w L) (star (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ)) := by
          rw [hIS K A S a _ (freeOf_matrix_transpose (freeOf_J_matrix a)), Jt_conj]
          exact c0
        simpa using c1.star_star
      refine ⟨?_, hkap, ?_, ?_, ?_⟩
      · rw [ePs]
        exact m1.mul hU'
      · rw [ePs, eRR, eJL, star_mul]
        simp only [mul_assoc]
        rw [m2, hcomm.left_comm, h3']
      · rw [ePs, eRR, eRRd, ekap, star_mul]
        have tw : ins a (TTw QQ (L ++ w) (Y - 1)) * Ps QQ q w L =
            ph L (Y - 1) • (Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y - 1))) :=
          ins_twine hfP (twine_entries (h5' (Y - 1) hR1 hregd))
        calc star (Ps QQ q w L) * star (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)ᵀ) *
              (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y * Ps QQ q w L)
            = star (Ps QQ q w L) * (star (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)ᵀ) *
              PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * Ps QQ q w L := by
              simp only [mul_assoc]
          _ = (qw q (L ++ w) (Y - 1))⁻¹ • (star (Ps QQ q w L) * RRw QQ (L ++ w) *
              (ins a (TTw QQ (L ++ w) (Y - 1)) * Ps QQ q w L)) := by
              rw [m3]
              simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
          _ = ((qw q (L ++ w) (Y - 1))⁻¹ * ph L (Y - 1)) • (star (Ps QQ q w L) * RRw QQ (L ++ w) *
              Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y - 1))) := by
              rw [tw, mul_smul_comm, smul_smul]
              simp only [mul_assoc]
          _ = (kap q w L * qw q (L ++ w) (Y - 1) / ph L (Y - 1))⁻¹ •
              (RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y - 1))) := by
              rw [h4', smul_mul_assoc, smul_smul]
              congr 1
              rw [inv_div]
              ring
      · intro Y0 hr1 hr2
        obtain ⟨hl1, hr1'⟩ := reg_cons hr1
        obtain ⟨hl2, hr2'⟩ := reg_cons hr2
        have n1 : Y - Y0 ≠ 1 := hl1
        have n2 : Y0 - Y ≠ 0 := by
          intro h
          exact hl2 (by change Y0 - (Y - 1) = 1; linear_combination h)
        have e1 : Y0 - (Y - 1) = Y0 - Y + 1 := by ring
        have eTT : TTw QQ ((⟨false, a, Y⟩ :: L) ++ w) Y0 = Rht0 a (Y - Y0) * TTw QQ (L ++ w) Y0 :=
          rfl
        have eTTd : TTw QQ ((⟨false, a, Y⟩ :: L).map dl ++ w) Y0 =
            TTw QQ (L.map dl ++ w) Y0 * Rh0 a (Y0 - (Y - 1)) := rfl
        have eph : ph (⟨false, a, Y⟩ :: L) Y0 = ph L Y0 * ((Y0 - Y) / (Y0 - Y + 1)) := rfl
        rw [ePs, eTT, eTTd, eph, diagScalar_mul, e1]
        calc Rht0 a (Y - Y0) * TTw QQ (L ++ w) Y0 *
              (d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * d0 (Ps QQ q w L))
            = (Rht0 a (Y - Y0) * TTw QQ (L ++ w) Y0 *
              d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y)) * d0 (Ps QQ q w L) :=
              (mul_assoc _ _ _).symm
          _ = ((Y0 - Y) / (Y0 - Y + 1)) • (d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (TTw QQ (L ++ w) Y0 * (Rh0 a (Y0 - Y + 1) * d0 (Ps QQ q w L)))) := by
              rw [m4 Y0 hr1' n1 n2, smul_mul_assoc]
              simp only [mul_assoc]
          _ = ((Y0 - Y) / (Y0 - Y + 1)) • (d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              ((TTw QQ (L ++ w) Y0 * d0 (Ps QQ q w L)) * Rh0 a (Y0 - Y + 1))) := by
              rw [Rh0_comm hfP]
              simp only [mul_assoc]
          _ = (ph L Y0 * ((Y0 - Y) / (Y0 - Y + 1))) •
              (d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * d0 (Ps QQ q w L) *
              (TTw QQ (L.map dl ++ w) Y0 * Rh0 a (Y0 - Y + 1))) := by
              rw [h5' Y0 hr1' hr2', smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm (ph L Y0)]
              simp only [mul_assoc]
    ·
      change Reg (L ++ w) (Y + 1) at hR1
      change qw q (L ++ w) Y ≠ 0 at hq
      change Reg (L.map dl ++ w) (Y + 1) at hregd
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hDP K A S {Y | Reg (L ++ w) Y} (RRw QQ (L ++ w))
        (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y hM hfR hfT hregY hR1 hstar hq
      have ePs : Ps QQ q w (⟨true, a, Y⟩ :: L) =
          PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y * Ps QQ q w L := rfl
      have eRR : RRw QQ ((⟨true, a, Y⟩ :: L) ++ w) =
          RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y) := rfl
      have eRRd : RRw QQ ((⟨true, a, Y⟩ :: L).map dl ++ w) =
          RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ := rfl
      have eJL : (JL (⟨true, a, Y⟩ :: L) : SlopeTestRemainingChoices S A) = ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) * JL L := rfl
      have ekap : kap q w (⟨true, a, Y⟩ :: L) = kap q w L * qw q (L ++ w) Y / ph L (Y + 1) := rfl
      have hcomm : Commute (star (Ps QQ q w L)) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) := by
        have c0 : Commute (Ps QQ q w L) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ) :=
          (hIF K A S a _).2 _ hfP (fun i j => J_entry_comm _ j i)
        have c1 : Commute (Ps QQ q w L) (star (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)))) := by
          rw [hIS K A S a _ (freeOf_J_matrix a), J_conj]
          exact c0
        simpa using c1.star_star
      refine ⟨?_, hkap, ?_, ?_, ?_⟩
      · rw [ePs]
        exact (show IsUnit (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) from
          ⟨⟨_, _, d2, d3⟩, rfl⟩).mul hU'
      · rw [ePs, eRR, eJL, star_mul]
        simp only [mul_assoc]
        rw [d4, hcomm.left_comm, h3']
      · rw [ePs, eRR, eRRd, ekap, star_mul]
        have tw : ins a (TTw QQ (L ++ w) (Y + 1))ᵀ * Ps QQ q w L =
            ph L (Y + 1) • (Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ) :=
          ins_twine hfP (fun i j => twine_entries (h5' (Y + 1) hR1 hregd) j i)
        calc star (Ps QQ q w L) * star (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)) *
              (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y * Ps QQ q w L)
            = star (Ps QQ q w L) * (star (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)) *
              PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * Ps QQ q w L := by
              simp only [mul_assoc]
          _ = (qw q (L ++ w) Y)⁻¹ • (star (Ps QQ q w L) * RRw QQ (L ++ w) *
              (ins a (TTw QQ (L ++ w) (Y + 1))ᵀ * Ps QQ q w L)) := by
              rw [d5]
              simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
          _ = ((qw q (L ++ w) Y)⁻¹ * ph L (Y + 1)) • (star (Ps QQ q w L) * RRw QQ (L ++ w) *
              Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ) := by
              rw [tw, mul_smul_comm, smul_smul]
              simp only [mul_assoc]
          _ = (kap q w L * qw q (L ++ w) Y / ph L (Y + 1))⁻¹ •
              (RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ) := by
              rw [h4', smul_mul_assoc, smul_smul]
              congr 1
              rw [inv_div]
              ring
      · intro Y0 hr1 hr2
        obtain ⟨hl1, hr1'⟩ := reg_cons hr1
        obtain ⟨hl2, hr2'⟩ := reg_cons hr2
        have n1 : Y0 - Y ≠ 1 := hl1
        have n2 : Y0 - Y ≠ 0 := by
          intro h
          exact hl2 (by change Y + 1 - Y0 = 1; linear_combination -h)
        have eTT : TTw QQ ((⟨true, a, Y⟩ :: L) ++ w) Y0 = TTw QQ (L ++ w) Y0 * Rh0 a (Y0 - Y) := rfl
        have eTTd : TTw QQ ((⟨true, a, Y⟩ :: L).map dl ++ w) Y0 =
            Rht0 a (Y + 1 - Y0) * TTw QQ (L.map dl ++ w) Y0 := rfl
        have eph : ph (⟨true, a, Y⟩ :: L) Y0 = ph L Y0 * ((Y0 - Y) / (Y0 - Y - 1)) := rfl
        rw [ePs, eTT, eTTd, eph, diagScalar_mul]
        calc TTw QQ (L ++ w) Y0 * Rh0 a (Y0 - Y) *
              (d0 (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * d0 (Ps QQ q w L))
            = (TTw QQ (L ++ w) Y0 * Rh0 a (Y0 - Y) *
              d0 (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y)) * d0 (Ps QQ q w L) :=
              (mul_assoc _ _ _).symm
          _ = ((Y0 - Y) / (Y0 - Y - 1)) • (d0 (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (Rht0 a (Y + 1 - Y0) * (TTw QQ (L ++ w) Y0 * d0 (Ps QQ q w L)))) := by
              rw [d6 Y0 hr1' n1 n2, smul_mul_assoc]
              simp only [mul_assoc]
          _ = (ph L Y0 * ((Y0 - Y) / (Y0 - Y - 1))) •
              (d0 (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * d0 (Ps QQ q w L) *
              (Rht0 a (Y + 1 - Y0) * TTw QQ (L.map dl ++ w) Y0)) := by
              rw [h5' Y0 hr1' hr2', mul_smul_comm, mul_smul_comm, smul_smul, mul_comm (ph L Y0)]
              rw [← mul_assoc (Rht0 a (Y + 1 - Y0)), Rht0_comm hfP]
              simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Wd10
