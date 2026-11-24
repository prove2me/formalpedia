-- Prove2me | solution 1 for Formalism.ZF.landauLocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:27.861953+00:00
-- url     : https://prove2.me/submissions/26baab87-dafc-4a1e-a400-40bb18a652d8

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivBound
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZeroFactor
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LandauLocalOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ThreeFourOne
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRight
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_SmallHeight
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZeroFreeOf
import Definitions.Def_Formalism_ZeroFreeRegion_FinalZFR
import Theorems.Thm_Formalism_ZF_localZeroExpansionOfFactorization
import Theorems.Thm_Formalism_ZF_logDerivBoundOnBall
import Theorems.Thm_Formalism_ZF_zeroFactorization


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
theorem _root_.solution : LandauLocal := localZeroExpansionOfFactorization zeroFactorization logDerivBoundOnBall
end Formalism.ZF
