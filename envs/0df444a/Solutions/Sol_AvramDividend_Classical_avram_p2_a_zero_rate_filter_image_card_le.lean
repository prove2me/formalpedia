-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_filter_image_card_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:10:02.880918+00:00
-- url     : https://prove2.me/submissions/055acd2c-e312-43b1-a265-c0076396b499

import Mathlib.Data.Finset.Card

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset

/-- Distinct marked grid endpoints are no more numerous than their marked
source cell indices, even if the time grid has collisions. -/
theorem solution
    {α β : Type*} [DecidableEq β] (s : Finset α)
    (f : α → β) (p : β → Prop) [DecidablePred p] :
    ((s.image f).filter p).card ≤
      (s.filter (fun a => p (f a))).card := by
  rw [Finset.filter_image]
  exact Finset.card_image_le
