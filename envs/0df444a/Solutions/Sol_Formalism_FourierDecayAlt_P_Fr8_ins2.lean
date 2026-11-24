-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.ins2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:23:38.888868+00:00
-- url     : https://prove2.me/submissions/aea78a5f-5c34-425f-9de6-62d38bb9869a

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution (a : S) (p q r s : SlopeTestRemainingChoices S A) :
    ins a !![p, q; r, s] = eU a 0 0 * p + eU a 0 1 * q + eU a 1 0 * r + eU a 1 1 * s := by
  simp [Formalism.FourierDecayAlt.Wd.ins, Fin.sum_univ_two, add_assoc]
end Formalism.FourierDecayAlt.P.Fr8
