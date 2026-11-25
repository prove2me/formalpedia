-- Prove2me | solution 1 for Formalism.L2.Th1.D.normUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:37:52.948139+00:00
-- url     : https://prove2.me/submissions/2a5edca5-93d2-473c-8cbd-6351ccc44786

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NonVac
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SecondLevelOfNormHolds
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_SecondLevelOfNorm
import Theorems.Thm_Formalism_L2_Th1_D_norm_units_alt


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
theorem _root_.solution : NormUnits := norm_units_alt
end Formalism.L2.Th1.D
