-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_public_drop_zero_original_jump_marks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:53:06.513983+00:00
-- url     : https://prove2.me/submissions/f9d9c972-c8a4-491b-9a9d-ab25a528e217

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped BigOperators

/-- Original zero jump marks can be removed from a finite exceptional set
without changing the actual infinite total magnitude of its complement. -/
theorem solution
    {ι : Type*} [DecidableEq ι] (j : ι → ℝ) (S : Finset ι) :
    ∃ T : Finset ι, (∀ i ∈ T, j i ≠ 0) ∧
      (∑' i : ι, if i ∈ T then 0 else |j i|) =
        (∑' i : ι, if i ∈ S then 0 else |j i|) := by
  classical
  refine ⟨S.filter (fun i => j i ≠ 0), ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · apply tsum_congr
    intro i
    by_cases hi : i ∈ S
    · by_cases hz : j i = 0
      · simp [Finset.mem_filter, hi, hz]
      · simp [Finset.mem_filter, hi, hz]
    · simp [Finset.mem_filter, hi]
