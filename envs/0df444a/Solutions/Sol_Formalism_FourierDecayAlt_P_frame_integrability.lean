-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.frame_integrability
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:43:29.140793+00:00
-- url     : https://prove2.me/submissions/70e01dd2-da20-4376-8b86-954af8e5ef4e

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_frameInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.P.PBD.FrameInt := Formalism.FourierDecayAlt.P.PBD.frameInt
end Formalism.FourierDecayAlt.P
