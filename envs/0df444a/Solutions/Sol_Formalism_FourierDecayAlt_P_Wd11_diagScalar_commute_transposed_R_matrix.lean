-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.diagScalar_commute_transposed_R_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:28:57.4095+00:00
-- url     : https://prove2.me/submissions/bb5e33c6-a26b-4664-8a7a-b7d4a09c681e

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_commute_of_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_rht_entry_comm

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
theorem _root_.solution {a : S} {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) (D : K) :
    Commute (d0 b) (Rht0 a D) := diagScalar_commute_of_entries (rht_entry_comm hb D)
end Formalism.FourierDecayAlt.P.Wd11
