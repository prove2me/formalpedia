-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd5.word_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:23.072218+00:00
-- url     : https://prove2.me/submissions/56036331-5ab7-4f56-87ee-ddc8936b9747

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_freeOf2_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_freeOf2_rmatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_freeOf2_rmatrix_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_freeOf2_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_freeOf2_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd5
open Matrix Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd5
theorem _root_.solution (QQ : K → M2 A) (w : List (Letter K S)) (c : S)
    (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) : FreeOf c (RRw QQ w) ∧ ∀ Y, FreeOf2 c (TTw QQ w Y) := by
  induction w with
  | nil => exact ⟨free_one c, fun Y => freeOf2_lift c (QQ Y)⟩
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    obtain ⟨hcl, hcw⟩ := hc
    obtain ⟨hR, hT⟩ := ih hcw
    have hT' : ∀ Y, FreeOf2 c (TTw QQ (l :: w) Y) := by
      intro Y
      simp only [TTw]
      split_ifs
      · exact freeOf2_mul (hT Y) (freeOf2_rmatrix hcl _)
      · exact freeOf2_mul (freeOf2_rmatrix_transpose hcl _) (hT Y)
    refine ⟨?_, hT'⟩
    simp only [RRw]
    apply free_mul hR
    apply free_ins hcl
    split_ifs
    · exact hT _
    · exact freeOf2_transpose (hT _)
end Formalism.FourierDecayAlt.P.Wd5
