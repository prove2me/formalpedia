-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gradient_small_near_critical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:42:32.976595+00:00
-- url     : https://prove2.me/submissions/fac87bba-f6d8-4ab4-a652-81079a935ae9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Theorems.Thm_Formalism_FourierDecayAlt_P_G1_gradSmall6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.GradSmall :=
  ⟨6, fun m D' hD x hx η hη hη' h => gradSmall6 m D' hD x hx η hη hη' h⟩
end Formalism.FourierDecayAlt.P
