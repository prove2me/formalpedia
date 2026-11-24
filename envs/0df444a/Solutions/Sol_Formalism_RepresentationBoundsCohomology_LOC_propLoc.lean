-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.propLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:16:29.10292+00:00
-- url     : https://prove2.me/submissions/df63a4c5-b03e-40ec-b789-cd6a0a652d77

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_LocDualOrth
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_QuotLen
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_PropLoc
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_locQuotLen
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_propLoc_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution : StatPropLoc.{u} := propLoc_of locQuotLen
end Formalism.RepresentationBoundsCohomology.LOC
