-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.marked_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:58.282972+00:00
-- url     : https://prove2.me/submissions/e73bff99-b74c-42c5-bb11-34c5017ee5b5

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
theorem _root_.solution (t : Finset ℕ) (r u s : ℕ) :
    Marked t r u s ↔ ∀ c ∈ Icc 1 (6 * r + 1), EC r u s c t := by
  unfold Marked EC
  simp only [mem_Icc, and_imp]
end Formalism.G0.TopsChoiceProbabilityLemmas
