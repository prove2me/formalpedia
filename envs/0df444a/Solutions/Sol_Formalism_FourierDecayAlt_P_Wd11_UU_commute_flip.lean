-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.UU_commute_flip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:28:04.7418+00:00
-- url     : https://prove2.me/submissions/503277c6-bd08-4c47-bead-49d2bfc5dc24

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
theorem _root_.solution (a : S) (s : K) :
    lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s))) * P0 a =
      P0 a * (lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s)))) := by
  rw [insL_Um]
  ext1 i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, lift0, d0, P0, Um, io_one, io_zero, io_neg,
      io_algebraMap, sub_mul, mul_sub, eU_mul_eU, smul_sub] <;> try module
end Formalism.FourierDecayAlt.P.Wd11
