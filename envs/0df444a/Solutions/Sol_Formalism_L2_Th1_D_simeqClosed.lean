-- Prove2me | solution 1 for Formalism.L2.Th1.D.simeqClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:13:47.451218+00:00
-- url     : https://prove2.me/submissions/4be2e751-0c70-4928-9a45-581bca60968a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ThetaIntegerIsSSubstitution
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TraceDualExists
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_TransportFirstLevel
import Theorems.Thm_Formalism_L2_Th1_D_simeq_closed


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
theorem _root_.solution : SimeqClosed := simeq_closed
end Formalism.L2.Th1.D
