-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.block_forcing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:34:24.980353+00:00
-- url     : https://prove2.me/submissions/d2178f2a-1796-43b7-b595-d50685237470

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_forcing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.Forcing := Formalism.FourierDecayAlt.P.S3x8.forcing
end Formalism.FourierDecayAlt.P
