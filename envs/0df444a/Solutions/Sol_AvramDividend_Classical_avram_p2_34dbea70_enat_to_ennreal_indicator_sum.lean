-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_enat_to_ennreal_indicator_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:33:04.772303+00:00
-- url     : https://prove2.me/submissions/015fe3fa-e3de-4037-b403-77ef539580b6

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
open scoped ENat ENNReal BigOperators

/-- ENat indicator sums convert exactly to ENNReal indicator sums. -/
theorem solution {α : Type*} [DecidableEq α]
    (s : Finset α) (marked : α → Prop) [DecidablePred marked] :
    ENat.toENNReal
      (∑ i ∈ s, (if marked i then (1 : ℕ∞) else 0)) =
        ∑ i ∈ s, (if marked i then (1 : ℝ≥0∞) else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hmark : marked a
      · simp [ha, hmark, ENat.toENNReal_add, ih]
      · simp [ha, hmark, ENat.toENNReal_add, ih]
