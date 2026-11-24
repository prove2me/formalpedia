-- Prove2me | solution 1 for Formalism.G0.many_orbits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:38.658492+00:00
-- url     : https://prove2.me/submissions/545d5177-039f-4d18-9d9f-aeec1e8abd02

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Theorems.Thm_Formalism_G0_manyOrbits_of
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
theorem _root_.solution : ManyOrbits := manyOrbits_of walkSharp_true
end Formalism.G0
