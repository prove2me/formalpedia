-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_filter_card_eq_enat_indicator_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:20:54.957207+00:00
-- url     : https://prove2.me/submissions/0a3f19a9-692c-4e2f-875b-44593f3cf0f2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
open scoped ENat BigOperators

/-- A finite marked-set count equals its ENat indicator sum. -/
theorem solution {α : Type*} [DecidableEq α]
    (s : Finset α) (marked : α → Prop) [DecidablePred marked] :
    ((s.filter marked).card : ℕ∞) =
      ∑ i ∈ s, (if marked i then (1 : ℕ∞) else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hmark : marked a
      · simp [ha, hmark, ih]
      · simp [ha, hmark, ih]
