-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.insL_Um
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:10:50.107724+00:00
-- url     : https://prove2.me/submissions/023d9cf7-f2af-4f9f-aa0c-92bc587e59fc

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_algebraMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_sum_eU_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution (a : S) (s : K) :
    (ins a (lift0 (Um (A := A) s)) : SlopeTestRemainingChoices S A) = 1 - s • eU a 1 0 := by
  rw [← sum_eU_diag a]
  unfold ins lift0
  simp [Fin.sum_univ_two, Um, io_one, io_zero, io_neg, io_algebraMap]
  abel
end Formalism.FourierDecayAlt.P.Wd11
