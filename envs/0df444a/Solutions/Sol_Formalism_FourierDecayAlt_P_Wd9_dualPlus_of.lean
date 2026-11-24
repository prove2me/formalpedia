-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.dualPlus_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:50.704812+00:00
-- url     : https://prove2.me/submissions/2258cdd0-ef08-49e9-82ca-dabf486542fd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_ins_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_J_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf2_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_J_mul_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_J_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_J_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_comm_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_diagScalar_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_diagScalar_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_diagScalar_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_diagScalar_commute_of_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_Rh0_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_star_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_ins_J_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_psiP_eq
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
theorem _root_.solution (hE : ExchMinus) : DualPlus := by
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q a Y hM hR hF hY hY1 hYr hq
  obtain ⟨c1, c2, c3⟩ := position_clauses TT q a Y hF (hM.det Y hY hY1) hq
  have hH : star (RR * ins a (TT Y)) = RR * ins a (TT Y) :=
    star_mul_ins hR (hF Y) (hM.herm Y hY hYr)
  have c4 : star (PsiP TT q a Y) * (RR * ins a (TT Y)) = ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) * RR := by
    rw [← hH, ← star_mul, mul_assoc, c1, star_mul, hM.form_herm,
      Wd1.ins_star a _ (freeOf2_transpose (freeOf_J_matrix a)), J_transpose, Matrix.conjTranspose_neg,
      J_conjTranspose, neg_neg]
  refine ⟨c1, c2, c3, c4, ?_, ?_⟩
  · rw [c4, ← ins_J_comm hR, mul_assoc, PsiP, ← Wd1.ins_mul a _ _ (freeOf_J_matrix a), Matrix.mul_neg,
      Matrix.mul_smul, ← Matrix.mul_assoc, J_mul_J, Matrix.neg_mul, Matrix.one_mul, smul_neg, neg_neg,
      ins_smul, mul_smul_comm]
  · intro Y0 hY0 hD1 hD0
    have hex := hE K A S Ω RR TT q a Y0 (Y + 1) hM hF hY0 hY1
    have hc : d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) * TT Y0 = TT Y0 * d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) :=
      diagScalar_commute_of_entries fun i j => (Wd1.ins_comm a _ (TT Y0 i j) (hF Y0 i j) (comm_J _)).symm
    have hk := Rh0_J (A := A) a (Y0 - Y) (Y + 1 - Y0) (by ring) hD0 hD1
    rw [psiP_eq, diagScalar_neg, diagScalar_smul, diagScalar_mul]
    generalize d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) = Jd at hc hk ⊢
    generalize d0 (ins a (TT (Y + 1))ᵀ) = Td at hex ⊢
    generalize (Rht0 a (Y + 1 - Y0) : M2 (SlopeTestRemainingChoices S A)) = R at hex hk ⊢
    generalize (Y0 - Y) / (Y0 - Y - 1) = c at hk ⊢
    calc TT Y0 * Rh0 a (Y0 - Y) * -((q Y)⁻¹ • (Jd * Td))
        = -((q Y)⁻¹ • (TT Y0 * (Rh0 a (Y0 - Y) * Jd) * Td)) := by
          simp only [Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_assoc]
      _ = -((q Y)⁻¹ • c • ((TT Y0 * Jd) * R * Td)) := by
          rw [hk]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = -((q Y)⁻¹ • c • (Jd * (TT Y0 * R * Td))) := by
          rw [← hc]; simp only [Matrix.mul_assoc]
      _ = -((q Y)⁻¹ • c • (Jd * (Td * R * TT Y0))) := by rw [hex]
      _ = c • (-((q Y)⁻¹ • (Jd * Td)) * (R * TT Y0)) := by
          simp only [Matrix.neg_mul, Matrix.smul_mul, smul_neg, Matrix.mul_assoc]
          rw [smul_comm]
end Formalism.FourierDecayAlt.P.Wd9
