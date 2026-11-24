-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.freeOf2_rmatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:38.813985+00:00
-- url     : https://prove2.me/submissions/7bdb9fb3-360b-459b-81be-118a34d77899

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_rh_entry_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_comm_of_ne


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
theorem _root_.solution {a c : S} (h : c ≠ a) (D : K) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) :=
  fun i j k l => rh_entry_comm (fun m n => (eU_comm_of_ne h k l m n).symm) D i j
end Formalism.FourierDecayAlt.P.Wd11
