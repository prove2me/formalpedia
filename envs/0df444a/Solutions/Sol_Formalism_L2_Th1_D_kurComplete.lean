-- Prove2me | solution 1 for Formalism.L2.Th1.D.kurComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:38:27.42156+00:00
-- url     : https://prove2.me/submissions/bf03ef4e-25bc-414c-b97e-4806d8bce059

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_TransportFirstLevel
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IntegralPartAtVariable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Theorems.Thm_Formalism_L2_Th1_D_unramified_completion_complete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
namespace Formalism.L2.Th1.D
theorem _root_.solution : KurComplete := unramified_completion_complete
end Formalism.L2.Th1.D
