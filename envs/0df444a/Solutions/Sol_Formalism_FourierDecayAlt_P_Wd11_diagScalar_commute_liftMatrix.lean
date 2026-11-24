-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.diagScalar_commute_liftMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:29:30.093192+00:00
-- url     : https://prove2.me/submissions/3e698295-6d7d-4f0d-a88a-c8085f2e3112

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_commute_of_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_cen

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
theorem _root_.solution {N : M2 A} (hN : Cen N) (b : SlopeTestRemainingChoices S A) : Commute (d0 b) (lift0 N) :=
  diagScalar_commute_of_entries fun i j => (io_cen (hN i j) b).symm
end Formalism.FourierDecayAlt.P.Wd11
