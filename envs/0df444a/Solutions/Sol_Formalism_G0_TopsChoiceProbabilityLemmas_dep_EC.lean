-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.dep_EC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:27.078032+00:00
-- url     : https://prove2.me/submissions/595a2526-d4d2-45af-9c11-73963f79a758

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution (r u s c : ℕ) : Dep (cell r u s c) (EC r u s c) := by
  intro t
  unfold EC
  rw [inter_assoc, inter_self]
end Formalism.G0.TopsChoiceProbabilityLemmas
