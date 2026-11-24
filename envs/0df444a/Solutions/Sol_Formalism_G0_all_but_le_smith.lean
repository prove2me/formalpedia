-- Prove2me | solution 1 for Formalism.G0.all_but_le_smith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:25.601926+00:00
-- url     : https://prove2.me/submissions/34f8b579-d4db-4747-b98a-c9b7b4d5e754

import Definitions.Def_Formalism_SubspaceCounting_StatementD
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_AllButLESmith
import Theorems.Thm_Formalism_G0_AllButLESmithP_key

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
open Module
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution : AllButLESmith := by
  unfold AllButLESmith
  intro O M ι _ _ _ _ _ _ π hπ P n snf g E
  exact AllButLESmithP.key snf π hπ g E _ (fun i => by simp)
end Formalism.G0
