-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.centre_block_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:36:37.060125+00:00
-- url     : https://prove2.me/submissions/3900ecad-2804-4884-8fb1-4dac2592a31b

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_centreBlocks

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.CentreBlocks := Formalism.FourierDecayAlt.P.S3x8.centreBlocks
end Formalism.FourierDecayAlt.P
