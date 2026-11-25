-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.big_cell_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:48.525475+00:00
-- url     : https://prove2.me/submissions/5b542e07-47c5-4d52-b3dc-49f2013cb7f0

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_bigCellFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.K.BigCellFree := Formalism.FourierDecayAlt.P.K.bigCellFree
end Formalism.FourierDecayAlt.P
