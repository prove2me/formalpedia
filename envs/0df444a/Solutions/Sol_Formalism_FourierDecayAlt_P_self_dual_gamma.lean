-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.self_dual_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:22.133841+00:00
-- url     : https://prove2.me/submissions/9b22c9e1-9646-47d8-8bc6-72bf792c3b42

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferProductMonic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Misc_selfDualG_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.I.SelfDualG := Formalism.FourierDecayAlt.P.Misc.selfDualG_holds
end Formalism.FourierDecayAlt.P
