-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.interlacing_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:47:16.236269+00:00
-- url     : https://prove2.me/submissions/c04c5ee1-be87-49c1-bcba-09469c908571

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_interlaceRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.I.InterlaceRatio := Formalism.FourierDecayAlt.P.Interlace.interlaceRatio
end Formalism.FourierDecayAlt.P
