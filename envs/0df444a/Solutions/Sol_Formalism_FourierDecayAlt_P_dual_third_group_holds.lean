-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dual_third_group_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:22.915221+00:00
-- url     : https://prove2.me/submissions/8fa3a89b-26ae-4964-83a2-d519323c836d

import Definitions.Def_Formalism_HermitianCurvature_StatementL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Dual_dual_third_group_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.L.DualLatticeInclusion := Formalism.FourierDecayAlt.P.Dual.dual_third_group_integral
end Formalism.FourierDecayAlt.P
