-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityWindows.window_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:00.211891+00:00
-- url     : https://prove2.me/submissions/8ce79ca3-8994-4d9b-a309-3f42a0683c41

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA

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
open Formalism.G0.TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsConditionalProbabilityWindows
theorem _root_.solution (n i L : ℕ) (hn : 1 ≤ n) : window n i L ⊆ range n := by
  intro x hx
  unfold window at hx
  obtain ⟨j, _, rfl⟩ := mem_image.1 hx
  exact mem_range.2 (Nat.mod_lt _ (by omega))
end Formalism.G0.TopsConditionalProbabilityWindows
