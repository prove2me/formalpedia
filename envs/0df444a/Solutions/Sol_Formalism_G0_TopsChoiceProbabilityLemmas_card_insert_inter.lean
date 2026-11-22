-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.card_insert_inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:17.395189+00:00
-- url     : https://prove2.me/submissions/f843b79d-2325-4bf8-b858-fc70fffa1650

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
theorem _root_.solution (a : ℕ) (t W : Finset ℕ) :
    (insert a t ∩ W).card ≤ (t ∩ W.erase a).card + 1 := by
  calc (insert a t ∩ W).card ≤ (insert a (t ∩ W.erase a)).card := card_le_card ?_
    _ ≤ _ := card_insert_le _ _
  intro x hx
  rw [mem_inter, mem_insert] at hx
  rw [mem_insert, mem_inter, mem_erase]
  by_cases h : x = a
  · left; exact h
  · right
    rcases hx with ⟨hx | hx, hw⟩
    · exact absurd hx h
    · exact ⟨hx, h, hw⟩
end Formalism.G0.TopsChoiceProbabilityLemmas
