-- Prove2me | solution 1 for Formalism.ZF.gzPNT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:26.021656+00:00
-- url     : https://prove2.me/submissions/c5c4529f-2eb0-4bd4-a5b4-fc58ca001b14

import Definitions.Def_Formalism_ZeroFreeRegion_FinalZFR
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRegionOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectDoublePole
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LaurentAtOne
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectShiftOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_GzPNTOf
import Definitions.Def_Formalism_ZeroFreeRegion_LogDerivRegion
import Theorems.Thm_Formalism_ZF_logDerivRegion
import Theorems.Thm_Formalism_ZF_rectShift
import Theorems.Thm_Formalism_ZF_logDerivBoundRightHalfPlane
import Theorems.Thm_Formalism_ZF_perron_formula
import Theorems.Thm_Formalism_ZF_zeroFreeRegion
import Theorems.Thm_Formalism_ZF_zetaPrimeSumErrorBoundOfBounds


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
theorem _root_.solution : GzPNT :=
  zetaPrimeSumErrorBoundOfBounds zeroFreeRegion logDerivRegion logDerivBoundRightHalfPlane perron_formula rectShift
end Formalism.ZF
