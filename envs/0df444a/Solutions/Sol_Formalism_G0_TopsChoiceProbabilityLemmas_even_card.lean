-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.even_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:57.878859+00:00
-- url     : https://prove2.me/submissions/e4dc06c5-1d8b-488e-8199-0ccaee90b093

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
theorem _root_.solution (a u : ℕ) : u / 2 ≤ ((Ico a (a + u)).filter Even).card := by
  have h := card_le_card_of_injOn (s := range (u / 2)) (t := (Ico a (a + u)).filter Even)
    (fun k => a + a % 2 + 2 * k) ?_ ?_
  · simpa using h
  · intro k hk
    simp only [coe_range, Set.mem_Iio] at hk
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ⟨a / 2 + a % 2 + k, by omega⟩⟩
  · intro k1 _ k2 _ h
    simp only at h
    omega
end Formalism.G0.TopsChoiceProbabilityLemmas
