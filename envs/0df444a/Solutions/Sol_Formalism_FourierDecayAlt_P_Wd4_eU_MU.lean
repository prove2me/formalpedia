-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.eU_MU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:12.321234+00:00
-- url     : https://prove2.me/submissions/58407750-ad90-460b-9b7a-67c267a88b86

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_mul_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_sum_eU_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd4
theorem _root_.solution (a : S) : MU (eU a : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A) where
  mul := Wd1.eU_mul_eU a
  sum := by
    have h := Wd1.sum_eU_diag (A := A) a
    rwa [Fin.sum_univ_two] at h
end Formalism.FourierDecayAlt.P.Wd4
