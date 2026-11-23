-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.freeOf_J_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:25.078071+00:00
-- url     : https://prove2.me/submissions/4e41efce-13ab-4fea-885f-bf19ccf86704

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_free_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_free_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_free_zero


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
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd10
theorem _root_.solution (a : S) : FreeOf2 a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact free_zero a
  · exact free_one a
  · exact free_neg (free_one a)
  · exact free_zero a
end Formalism.FourierDecayAlt.P.Wd10
