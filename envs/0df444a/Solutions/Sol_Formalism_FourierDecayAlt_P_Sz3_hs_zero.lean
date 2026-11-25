-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.hs_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:40:23.348931+00:00
-- url     : https://prove2.me/submissions/e14a7232-32f7-4ca9-863c-b15de91bacea

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution : hs 0 = 0 := by simp [hs]
end Formalism.FourierDecayAlt.P.Sz3
