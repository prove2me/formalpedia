-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingSeparatedFailureEnvelope_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:04.736325+00:00
-- url     : https://prove2.me/submissions/cedad488-5c81-4a4c-a0c9-bb6c3c4faf56

import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
import Theorems.Thm_FirstPassageLinearTransport_card_biUnion_le_sum


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) (M L S : ℕ) :
    (shrinkingSeparatedFailureEnvelope P M L S).card ≤
      (shellInitialWindowBad M (shrinkingHighTolerance P M M)).card +
      ∑ q ∈ Finset.Icc (S + 1) (M - 1),
        (shrinkingFirstBadSourcesAtRank P M S q).card +
      ∑ q ∈ Finset.Icc L S,
        (shrinkingFirstBadSourcesAtRank P M S q).card := by
  classical
  unfold shrinkingSeparatedFailureEnvelope
  calc
    _ ≤ (shellInitialWindowBad M (shrinkingHighTolerance P M M) ∪
        ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
          shrinkingFirstBadSourcesAtRank P M S q)).card +
        ((Finset.Icc L S).biUnion fun q =>
          shrinkingFirstBadSourcesAtRank P M S q).card :=
      Finset.card_union_le _ _
    _ ≤ ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card +
        ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
          shrinkingFirstBadSourcesAtRank P M S q).card) +
        ((Finset.Icc L S).biUnion fun q =>
          shrinkingFirstBadSourcesAtRank P M S q).card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ (shellInitialWindowBad M (shrinkingHighTolerance P M M)).card +
        ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          (shrinkingFirstBadSourcesAtRank P M S q).card +
        ∑ q ∈ Finset.Icc L S,
          (shrinkingFirstBadSourcesAtRank P M S q).card := by
      apply Nat.add_le_add
      · exact Nat.add_le_add_left
          (card_biUnion_le_sum (Finset.Icc (S + 1) (M - 1)) fun q =>
            shrinkingFirstBadSourcesAtRank P M S q) _
      · exact card_biUnion_le_sum (Finset.Icc L S) fun q =>
          shrinkingFirstBadSourcesAtRank P M S q
end FirstPassageLinearTransport
