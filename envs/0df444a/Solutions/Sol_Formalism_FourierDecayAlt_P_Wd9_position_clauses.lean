-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.position_clauses
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:11.773472+00:00
-- url     : https://prove2.me/submissions/f6dcec4c-b85c-4acd-a924-a05842c4319e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_J_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf2_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_matrix_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_matrix_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_J_mul_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_J_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_alg_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_one
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
theorem _root_.solution (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Y : K)
    (hF : ∀ Y, FreeOf2 a (TT Y)) (hdet : DetAt TT q Y) (hq : q Y ≠ 0) :
    ins a (TT Y) * PsiP TT q a Y = ins a JJᵀ ∧
    PsiP TT q a Y * ins a (JJ * TT Y) = 1 ∧
    ins a (JJ * TT Y) * PsiP TT q a Y = 1 := by
  obtain ⟨h1, h2⟩ := hdet
  rw [alg_smul] at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [PsiP, ← Wd1.ins_mul a _ _ (hF Y)]
    congr 1
    rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, h2, smul_smul, inv_mul_cancel₀ hq,
      one_smul, J_transpose]
  · rw [PsiP, ← Wd1.ins_mul a _ _
      (freeOf_matrix_neg (freeOf_matrix_smul _ (freeOf2_mul (freeOf_J_matrix a) (freeOf2_transpose (hF (Y + 1))))))]
    rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ JJ, h1,
      Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hq, one_smul, J_mul_J, neg_neg, Wd1.ins_one]
  · rw [PsiP, ← Wd1.ins_mul a _ _ (freeOf2_mul (freeOf_J_matrix a) (hF Y))]
    rw [Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_assoc, ← Matrix.mul_assoc (TT Y), h2,
      Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hq, one_smul, J_mul_J, neg_neg, Wd1.ins_one]
end Formalism.FourierDecayAlt.P.Wd9
