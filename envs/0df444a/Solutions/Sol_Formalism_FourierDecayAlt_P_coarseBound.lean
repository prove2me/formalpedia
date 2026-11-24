-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.coarseBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:28.72794+00:00
-- url     : https://prove2.me/submissions/5a525ba0-89cf-4b51-940c-3cb58c20ac83

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecText_recT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.RecursionText := Formalism.FourierDecayAlt.P.RecText.recT
end Formalism.FourierDecayAlt.P
