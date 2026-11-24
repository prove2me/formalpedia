-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.diagScalar_insert_commute_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:29:37.168682+00:00
-- url     : https://prove2.me/submissions/aa566c8c-4eef-499c-8eac-8f9210a70ae3

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_commute_of_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_comm_insL

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
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution {a : S} {N : M2 A} (hN : Cen N) {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) :
    Commute (d0 (ins a (lift0 N))) M :=
  diagScalar_commute_of_entries fun i j => (comm_insL hN (hM i j)).symm
end Formalism.FourierDecayAlt.P.Wd11
