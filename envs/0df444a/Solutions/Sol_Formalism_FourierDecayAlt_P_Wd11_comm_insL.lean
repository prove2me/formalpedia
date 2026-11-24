-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.comm_insL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:07:00.049857+00:00
-- url     : https://prove2.me/submissions/d00a16bd-1440-4f92-9394-6decdb964548

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_cen
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_comm


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
theorem _root_.solution {a : S} {N : M2 A} (hN : Cen N) {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) :
    Commute b (ins a (lift0 N)) :=
  ins_comm a _ b hb fun i j => (io_cen (hN i j) b).symm
end Formalism.FourierDecayAlt.P.Wd11
