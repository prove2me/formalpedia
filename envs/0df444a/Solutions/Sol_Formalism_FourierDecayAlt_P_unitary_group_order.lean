-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unitary_group_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:49:21.622454+00:00
-- url     : https://prove2.me/submissions/2675dfa7-1264-43e9-8624-1e8b053310b9

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_unitaryOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.UnitaryOrder := S3x6.d_unitaryOrder
end Formalism.FourierDecayAlt.P
