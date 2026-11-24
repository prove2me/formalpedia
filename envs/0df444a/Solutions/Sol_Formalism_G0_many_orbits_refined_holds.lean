-- Prove2me | solution 1 for Formalism.G0.many_orbits_refined_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:47.307796+00:00
-- url     : https://prove2.me/submissions/15e69c42-6414-4f3b-a337-3669cc0a2759

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbitsRefined
import Theorems.Thm_Formalism_G0_many_orbits_refined_of
import Theorems.Thm_Formalism_G0_walkSharp_true


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution : ManyOrbitsRefined := many_orbits_refined_of walkSharp_true
end Formalism.G0
