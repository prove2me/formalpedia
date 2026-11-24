-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.rht_entry_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:51:08.395665+00:00
-- url     : https://prove2.me/submissions/3d788993-51b5-4584-891d-bb8835a9bfe1

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix

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
theorem _root_.solution {a : S} {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) (D : K) (i j : Fin 2) :
    Commute b ((Rht0 a D : M2 (SlopeTestRemainingChoices S A)) i j) := by
  unfold Rht0 Q0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply]
  refine Commute.smul_right (Commute.sub_right (Commute.smul_right ?_ _) (hb i j).symm) _
  split_ifs
  · exact Commute.one_right _
  · exact Commute.zero_right _
end Formalism.FourierDecayAlt.P.Wd11
