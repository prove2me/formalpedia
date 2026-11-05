-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_public_original_abs_jump_finite_tail_lt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:36:54.987697+00:00
-- url     : https://prove2.me/submissions/d366d4e3-f3cd-4433-b9a0-a9f313e3da1e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped BigOperators

/-- The absolutely summable original jump magnitudes have an arbitrarily
small complement of a finite set of actual marked source times. -/
theorem solution
    {ι : Type*} (j : ι → ℝ)
    (hj : Summable (fun i => |j i|))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset ι, (∑' i : {i : ι // i ∉ S}, |j i.1|) < ε := by
  have ht : Filter.Tendsto
      (fun S : Finset ι => ∑ i ∈ S, |j i|)
      Filter.atTop (nhds (∑' i : ι, |j i|)) := hj.hasSum
  have hc : ∀ᶠ S : Finset ι in Filter.atTop,
      (∑' i : ι, |j i|) - ε < ∑ i ∈ S, |j i| :=
    ht.eventually (eventually_gt_nhds (sub_lt_self _ hε))
  obtain ⟨S, hS⟩ := hc.exists
  refine ⟨S, ?_⟩
  have hsplit := hj.sum_add_tsum_subtype_compl S
  linarith
