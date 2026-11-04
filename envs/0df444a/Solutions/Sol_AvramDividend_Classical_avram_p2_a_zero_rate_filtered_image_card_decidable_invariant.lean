-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_filtered_image_card_decidable_invariant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:33:19.014231+00:00
-- url     : https://prove2.me/submissions/77b54f32-1a5a-4006-9722-5e782ea7cd8c

import Mathlib.Data.Finset.Image
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finset_image_decidable_invariant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset AvramDividend.Classical

/-- Filtered grid image cardinality is invariant under the choice of equality decider. -/
theorem solution
    {α β : Type*} (s : Finset α) (f : α → β) (p : β → Prop)
    [DecidablePred p] (d₁ d₂ : DecidableEq β) :
    ((@Finset.image α β d₁ f s).filter p).card =
      ((@Finset.image α β d₂ f s).filter p).card := by
  rw [avram_p2_a_zero_rate_finset_image_decidable_invariant s f d₁ d₂]
