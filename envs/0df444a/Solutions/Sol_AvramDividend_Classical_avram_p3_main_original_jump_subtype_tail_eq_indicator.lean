-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_jump_subtype_tail_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:21:20.262389+00:00
-- url     : https://prove2.me/submissions/c09356eb-c714-451e-9ad5-09352d71072c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped BigOperators

/-- Original jump magnitudes outside finitely many marks are precisely their
indicator-supported whole-index tsum; the original summability is retained. -/
theorem solution
    {ι : Type*} [DecidableEq ι] (j : ι → ℝ) (S : Finset ι)
    (hj : Summable (fun i => |j i|)) :
    (∑' i : {i : ι // i ∉ S}, |j i.1|) =
      (∑' i : ι, if i ∈ S then 0 else |j i|) := by
  classical
  let t : Set ι := {i | i ∉ S}
  let g : ι → ℝ := fun i => if i ∈ S then 0 else |j i|
  have hsupport : Function.support g ⊆ t := by
    intro i hi
    change i ∉ S
    intro hmem
    have hz : g i = 0 := by simp [g, hmem]
    exact hi hz
  have htsum : (∑' i : t, g i.1) = ∑' i : ι, g i :=
    tsum_subtype_eq_of_support_subset hsupport
  calc
    (∑' i : {i : ι // i ∉ S}, |j i.1|) =
        (∑' i : t, g i.1) := by
          apply tsum_congr
          intro i
          simp [g, i.property]
    _ = ∑' i : ι, g i := htsum
    _ = (∑' i : ι, if i ∈ S then 0 else |j i|) := rfl
