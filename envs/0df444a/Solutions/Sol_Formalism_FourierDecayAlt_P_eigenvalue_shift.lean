-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.eigenvalue_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:35:45.109357+00:00
-- url     : https://prove2.me/submissions/9e3874ab-9832-40bc-b1b3-af05d4782970

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdExponentEstimate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.EigenShift := by
  intro k r Y a i; unfold Formalism.FourierDecayAlt.Q.uC C7.lamOf C7.nOf Formalism.FourierDecayAlt.Q.mdim; simp; ring
end Formalism.FourierDecayAlt.P
