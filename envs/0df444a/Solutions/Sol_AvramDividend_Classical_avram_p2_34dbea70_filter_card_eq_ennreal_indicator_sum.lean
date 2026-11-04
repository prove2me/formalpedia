-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_filter_card_eq_ennreal_indicator_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:17:25.387564+00:00
-- url     : https://prove2.me/submissions/f855ba7b-0120-4f04-b734-b3608e3372ef

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
open scoped ENNReal BigOperators

/-- An ENNReal indicator sum exactly counts a finite set's marked cells. -/
theorem solution {α : Type*} [DecidableEq α]
    (s : Finset α) (marked : α → Prop) [DecidablePred marked] :
    ((s.filter marked).card : ℝ≥0∞) =
      ∑ i ∈ s, (if marked i then (1 : ℝ≥0∞) else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hmark : marked a
      · simp [ha, hmark, ih]
      · simp [ha, hmark, ih]
