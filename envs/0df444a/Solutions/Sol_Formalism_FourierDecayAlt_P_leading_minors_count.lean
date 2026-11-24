-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.leading_minors_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:34.402453+00:00
-- url     : https://prove2.me/submissions/f0cdf829-881d-4df1-8197-f94f5bda66c2

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
import Theorems.Thm_Formalism_FourierDecayAlt_P_Minors_card_lead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LeadingMinorsCount := by
  intro K _ _ r
  exact Formalism.FourierDecayAlt.P.Minors.card_lead r
end Formalism.FourierDecayAlt.P
