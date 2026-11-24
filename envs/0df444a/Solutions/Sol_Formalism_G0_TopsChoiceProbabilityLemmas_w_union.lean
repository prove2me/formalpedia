-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.w_union
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:21.607295+00:00
-- url     : https://prove2.me/submissions/b49c2f3b-8d6d-486c-909c-09eeaf863f06

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
theorem _root_.solution {S R a b : Finset ℕ} (δ : ℝ) (h : Disjoint S R) (ha : a ⊆ S) (hb : b ⊆ R) :
    δ ^ (a ∪ b).card * (1 - δ) ^ ((S ∪ R).card - (a ∪ b).card) =
      (δ ^ a.card * (1 - δ) ^ (S.card - a.card)) * (δ ^ b.card * (1 - δ) ^ (R.card - b.card)) := by
  have hab : Disjoint a b := disjoint_of_subset_left ha (disjoint_of_subset_right hb h)
  rw [card_union_of_disjoint hab, card_union_of_disjoint h]
  have h1 := card_le_card ha
  have h2 := card_le_card hb
  rw [show S.card + R.card - (a.card + b.card) = (S.card - a.card) + (R.card - b.card) by omega,
    pow_add, pow_add]
  ring
end Formalism.G0.TopsChoiceProbabilityLemmas
