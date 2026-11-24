-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.insL_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:40.993033+00:00
-- url     : https://prove2.me/submissions/f0262ba5-a58c-4316-a3e1-9f408933d2a8

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_liftMatrix_diagonal_eq_diagScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_insert_diagonal_extract


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
theorem _root_.solution (a : S) (f : A) :
    (ins a (lift0 (Matrix.diagonal fun _ => f)) : SlopeTestRemainingChoices S A) = io f := by
  rw [liftMatrix_diagonal_eq_diagScalar, insert_diagonal_extract]
end Formalism.FourierDecayAlt.P.Wd11
