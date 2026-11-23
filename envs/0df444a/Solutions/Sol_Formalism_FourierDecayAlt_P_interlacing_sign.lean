-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.interlacing_sign
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:43.463702+00:00
-- url     : https://prove2.me/submissions/3444c960-e6e0-4385-8109-c9942fc052c8

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_interlaceSign

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.I.InterlaceSign := Formalism.FourierDecayAlt.P.Interlace.interlaceSign
end Formalism.FourierDecayAlt.P
