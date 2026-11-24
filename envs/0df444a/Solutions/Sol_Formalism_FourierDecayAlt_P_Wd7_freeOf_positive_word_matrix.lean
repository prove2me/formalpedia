-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.freeOf_positive_word_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:02.261968+00:00
-- url     : https://prove2.me/submissions/b1ab55aa-ab08-40ba-9fe3-161d3c933279

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_rmatrix

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
theorem _root_.solution {c : S} (w : List (Letter K S)) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) (Y : K) :
    FreeOf2 c (Xp w Y : M2 (SlopeTestRemainingChoices S A)) := by
  induction w with
  | nil => exact freeOf2_one c
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    by_cases h : l.plus
    · simp only [Xp, h, if_true]
      exact freeOf2_mul (ih hc.2) (freeOf2_rmatrix hc.1 _)
    · simp only [Xp, h]
      exact ih hc.2
end Formalism.FourierDecayAlt.P.Wd7
