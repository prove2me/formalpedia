-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.centreForcing_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:36:32.891597+00:00
-- url     : https://prove2.me/submissions/fa7a1bb1-9a56-4fbd-b41e-4b642c2a58d5

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_centreForcing

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.CentreForcing := Formalism.FourierDecayAlt.P.S3x8.centreForcing
end Formalism.FourierDecayAlt.P
