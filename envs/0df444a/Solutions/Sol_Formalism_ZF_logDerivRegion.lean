-- Prove2me | solution 1 for Formalism.ZF.logDerivRegion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:06:24.394813+00:00
-- url     : https://prove2.me/submissions/3c475830-4c02-4d50-bd26-0578fe5f9b78

import Definitions.Def_Formalism_ZeroFreeRegion_FinalZFR
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRegionOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectDoublePole
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LaurentAtOne
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectShiftOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_GzPNTOf
import Definitions.Def_Formalism_ZeroFreeRegion_LogDerivRegion
import Theorems.Thm_Formalism_ZF_growthBound
import Theorems.Thm_Formalism_ZF_landauLocal
import Theorems.Thm_Formalism_ZF_logDerivBoundInRegionOfBounds
import Theorems.Thm_Formalism_ZF_logDerivBoundRightHalfPlane
import Theorems.Thm_Formalism_ZF_logDerivBoundedHeight
import Theorems.Thm_Formalism_ZF_zeroFreeRegion
import Theorems.Thm_Formalism_ZF_zetaInvBound_statement


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : LogDerivRegion :=
  logDerivBoundInRegionOfBounds zeroFreeRegion logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    logDerivBoundedHeight landauLocal
end Formalism.ZF
