-- Prove2me | solution 1 for Formalism.ZF.rectShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:28:46.109303+00:00
-- url     : https://prove2.me/submissions/cb5255dc-b82c-40df-b311-38dfd2847a07

import Definitions.Def_Formalism_ZeroFreeRegion_FinalZFR
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRegionOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectDoublePole
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LaurentAtOne
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectShiftOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_GzPNTOf
import Definitions.Def_Formalism_ZeroFreeRegion_LogDerivRegion
import Theorems.Thm_Formalism_ZF_laurentExpansionAtOne
import Theorems.Thm_Formalism_ZF_rectangleShiftOfResidue
import Theorems.Thm_Formalism_ZF_rectangle_double_pole


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
theorem _root_.solution : RectShift := rectangleShiftOfResidue rectangle_double_pole laurentExpansionAtOne
end Formalism.ZF
