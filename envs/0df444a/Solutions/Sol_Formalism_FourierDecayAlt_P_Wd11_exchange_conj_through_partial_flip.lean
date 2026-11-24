-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.exchange_conj_through_partial_flip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:28:05.883929+00:00
-- url     : https://prove2.me/submissions/3012e240-6a65-4684-b813-1764ddbdb865

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_algebraMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_mul_eU


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
theorem _root_.solution (b : S) (s : K) :
    d0 (ins b (lift0 (Um (A := A) (star s)))) * Q0 b * lift0 (Um (A := A) s)ᴴ =
      lift0 (Um (A := A) s)ᴴ * Q0 b * d0 (ins b (lift0 (Um (A := A) (star s)))) := by
  rw [insL_Um]
  ext1 i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, lift0, d0, Q0, Um, io_one, io_zero, io_neg,
      io_algebraMap, sub_mul, mul_sub, add_mul, neg_mul, eU_mul_eU, ← algebraMap_star_comm] <;>
    try module
end Formalism.FourierDecayAlt.P.Wd11
