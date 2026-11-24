-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.tile_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:20.854402+00:00
-- url     : https://prove2.me/submissions/166b9e0d-adc6-4ebd-a36a-126c6080dfbb

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
theorem _root_.solution {r u s s' : ℕ} (h : s ≠ s') : Disjoint (tile r u s) (tile r u s') := by
  unfold tile
  rcases lt_or_gt_of_ne h with h | h
  · have := Nat.mul_le_mul_right ((6 * r + 1) * u) (show s + 1 ≤ s' by omega)
    exact disjoint_left.2 fun x hx hx' => by rw [mem_Ico] at hx hx'; omega
  · have := Nat.mul_le_mul_right ((6 * r + 1) * u) (show s' + 1 ≤ s by omega)
    exact disjoint_left.2 fun x hx hx' => by rw [mem_Ico] at hx hx'; omega
end Formalism.G0.TopsChoiceProbabilityLemmas
