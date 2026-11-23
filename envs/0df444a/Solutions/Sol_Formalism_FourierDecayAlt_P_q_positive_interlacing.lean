-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.q_positive_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:22:45.133389+00:00
-- url     : https://prove2.me/submissions/a8b305b8-9d40-4f89-8b97-2723508ff6c9

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_qPositive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.I.QPositive := Formalism.FourierDecayAlt.P.Interlace.qPositive
end Formalism.FourierDecayAlt.P
