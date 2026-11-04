-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_finset_image_decidable_invariant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:19:27.817338+00:00
-- url     : https://prove2.me/submissions/76acf57b-125f-4021-a803-b39c26c318d6

import Mathlib.Data.Finset.Image

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset

/-- A finite image does not depend on its equality-decision implementation. -/
theorem solution
    {α β : Type*} (s : Finset α) (f : α → β)
    (d₁ d₂ : DecidableEq β) :
    (@Finset.image α β d₁ f s) = (@Finset.image α β d₂ f s) := by
  apply Finset.ext
  intro b
  simp only [Finset.mem_image]
