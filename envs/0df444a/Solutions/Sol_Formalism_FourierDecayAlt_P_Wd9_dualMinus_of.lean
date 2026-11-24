-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.dualMinus_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:50.004408+00:00
-- url     : https://prove2.me/submissions/16da4c4c-40d0-4746-8e22-1b0277dee526

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_ins_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_ins_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_J_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf2_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_J_mul_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_J_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_J_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_comm_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_diagScalar_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_diagScalar_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_diagScalar_commute_of_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_Rht0_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_alg_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_star_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_herm_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_ins_J_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_psiM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_position_clauses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd9
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))
namespace Formalism.FourierDecayAlt.P.Wd9
theorem _root_.solution (hE : ExchPlus) : DualMinus := by
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q a Yb hM hR hF hYb hYb1 hYr hq
  have hdet : DetAt TT q (Yb - 1) := hM.det (Yb - 1) hYb1 (by rwa [sub_add_cancel])
  obtain ⟨-, c2, c3⟩ := position_clauses TT q a (Yb - 1) hF hdet hq
  obtain ⟨h1, -⟩ := hdet
  rw [alg_smul, sub_add_cancel] at h1
  have hH : star (RR * ins a (TT Yb)ᵀ) = RR * ins a (TT Yb)ᵀ :=
    star_mul_ins hR (freeOf2_transpose (hF Yb)) (herm_transpose (hM.herm Yb hYb hYr))
  have hP : PsiM TT q a Yb = (q (Yb - 1))⁻¹ • ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * TT (Yb - 1)) := by
    rw [PsiM, ins_smul]
  have c0 : ins a (TT Yb)ᵀ * PsiM TT q a Yb = ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) := by
    rw [PsiM, ← Wd1.ins_mul a _ _ (freeOf2_transpose (hF Yb)), Matrix.mul_smul, ← Matrix.mul_assoc, h1,
      smul_smul, inv_mul_cancel₀ hq, one_smul]
  have c4 : star (PsiM TT q a Yb) * (RR * ins a (TT Yb)ᵀ) = ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ * RR := by
    rw [← hH, ← star_mul, mul_assoc, c0, star_mul, hM.form_herm,
      Wd1.ins_star a _ (freeOf_J_matrix a), J_transpose, J_conjTranspose]
  refine ⟨?_, c4, ?_, ?_⟩
  · refine ⟨⟨PsiM TT q a Yb, q (Yb - 1) • PsiP TT q a (Yb - 1), ?_, ?_⟩, rfl⟩
    · rw [hP, smul_mul_smul_comm, c3, inv_mul_cancel₀ hq, one_smul]
    · rw [hP, smul_mul_smul_comm, c2, mul_inv_cancel₀ hq, one_smul]
  · rw [c4, J_transpose, ins_neg, neg_mul, ← ins_J_comm hR, neg_mul, mul_assoc, PsiM,
      ← Wd1.ins_mul a _ _ (freeOf_J_matrix a), Matrix.mul_smul, ← Matrix.mul_assoc, J_mul_J, Matrix.neg_mul,
      Matrix.one_mul, smul_neg, ins_neg, mul_neg, neg_neg, ins_smul, mul_smul_comm]
  · intro Y0 hY0 hd1 hd0
    have hex := hE K A S Ω RR TT q a Y0 (Yb - 1) hM hF hY0 hYb1
    rw [show Y0 - (Yb - 1) = Y0 - Yb + 1 by ring] at hex
    have hc : d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) * TT Y0 = TT Y0 * d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) :=
      diagScalar_commute_of_entries fun i j => (Wd1.ins_comm a _ (TT Y0 i j) (hF Y0 i j) (comm_J _)).symm
    have hd0' : Yb - Y0 ≠ 0 := fun h => hd0 (by rw [← neg_sub, h, neg_zero])
    have hk := Rht0_J (A := A) a (Yb - Y0) (Y0 - Yb + 1) (by ring) hd0' hd1
    rw [show (Yb - Y0) / (Yb - Y0 - 1) = (Y0 - Yb) / (Y0 - Yb + 1) by
      rw [← neg_div_neg_eq]; congr 1 <;> ring] at hk
    rw [psiM_eq, diagScalar_smul, diagScalar_mul]
    generalize d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) = Jd at hc hk ⊢
    generalize d0 (ins a (TT (Yb - 1))) = Td at hex ⊢
    generalize (Rh0 a (Y0 - Yb + 1) : M2 (SlopeTestRemainingChoices S A)) = R at hex hk ⊢
    generalize (Y0 - Yb) / (Y0 - Yb + 1) = c at hk ⊢
    calc Rht0 a (Yb - Y0) * TT Y0 * ((q (Yb - 1))⁻¹ • (Jd * Td))
        = (q (Yb - 1))⁻¹ • (Rht0 a (Yb - Y0) * (TT Y0 * Jd) * Td) := by
          simp only [Matrix.mul_smul, Matrix.mul_assoc]
      _ = (q (Yb - 1))⁻¹ • ((Rht0 a (Yb - Y0) * Jd) * TT Y0 * Td) := by
          rw [← hc]; simp only [Matrix.mul_assoc]
      _ = (q (Yb - 1))⁻¹ • c • (Jd * (R * TT Y0 * Td)) := by
          rw [hk]; simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (q (Yb - 1))⁻¹ • c • (Jd * (Td * TT Y0 * R)) := by rw [hex]
      _ = c • ((q (Yb - 1))⁻¹ • (Jd * Td) * (TT Y0 * R)) := by
          simp only [Matrix.smul_mul, Matrix.mul_assoc]
          rw [smul_comm]
end Formalism.FourierDecayAlt.P.Wd9
