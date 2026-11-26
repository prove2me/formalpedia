-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutSeparatedFailureEnvelope_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:43:00.257801+00:00
-- url     : https://prove2.me/submissions/d7430b19-dd3c-41f5-a732-a6a6261d4bbe

import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
import Theorems.Thm_FirstPassageLinearTransport_card_biUnion_le_sum


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (K₀ : ℝ) (M L S : ℕ) :
    (timeoutSeparatedFailureEnvelope P K₀ M L S).card ≤
      (shellInitialWindowBad M (timeoutHighTolerance P M M)).card +
      ∑ q ∈ Finset.Icc (S + 1) (M - 1),
        (timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card +
      ∑ p ∈ Finset.Icc (L + 1) S,
        (timeoutFirstBadSourcesAtRank P K₀ L M S p).card := by
  classical
  unfold timeoutSeparatedFailureEnvelope
  calc
    _ ≤ (shellInitialWindowBad M (timeoutHighTolerance P M M) ∪
        ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
          timeoutHighFirstBadSourcesAtRank P K₀ L M S q)).card +
        ((Finset.Icc (L + 1) S).biUnion fun p =>
          timeoutFirstBadSourcesAtRank P K₀ L M S p).card :=
      Finset.card_union_le _ _
    _ ≤ (shellInitialWindowBad M (timeoutHighTolerance P M M)).card +
        ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
          timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card +
        ((Finset.Icc (L + 1) S).biUnion fun p =>
          timeoutFirstBadSourcesAtRank P K₀ L M S p).card := by
      have hfirst := Finset.card_union_le
        (shellInitialWindowBad M (timeoutHighTolerance P M M))
        ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
          timeoutHighFirstBadSourcesAtRank P K₀ L M S q)
      omega
    _ ≤ _ := by
      have hHigh := card_biUnion_le_sum (Finset.Icc (S + 1) (M - 1))
        (fun q => timeoutHighFirstBadSourcesAtRank P K₀ L M S q)
      have hLow := card_biUnion_le_sum (Finset.Icc (L + 1) S)
        (fun p => timeoutFirstBadSourcesAtRank P K₀ L M S p)
      omega
end FirstPassageLinearTransport
