-- Prove2me | solution 1 for Formalism.MainNotions.G.WittPI.wittIdentity_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:46:14.008154+00:00
-- url     : https://prove2.me/submissions/dfdf34f4-740d-47df-a9e8-472dff809f8f

import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittUnram
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjBridge
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_WittIdentPI
import Theorems.Thm_Formalism_MainNotions_G_WittPI_wittIdent_of
import Theorems.Thm_witt_unramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.WittPI
namespace Formalism.MainNotions.G.WittPI
theorem _root_.solution : Formalism.MainNotions.G.WittIdent := wittIdent_of witt_unramified
end Formalism.MainNotions.G.WittPI
