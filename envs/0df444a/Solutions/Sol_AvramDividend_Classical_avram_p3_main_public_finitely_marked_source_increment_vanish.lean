-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_public_finitely_marked_source_increment_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:37:00.103655+00:00
-- url     : https://prove2.me/submissions/83af5cb3-feba-4ee6-845b-58469f8ff270

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped BigOperators

/-- A finite family of marked source increments vanishes in total variation. -/
theorem solution
    {ι : Type*} (S : Finset ι) (c : ℕ → ι → ℝ)
    (hc : ∀ i ∈ S, Filter.Tendsto (fun k => c k i) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∑ i ∈ S, |c k i|) Filter.atTop (nhds 0) := by
  have hone (i : ι) (hi : i ∈ S) :
      Filter.Tendsto (fun k => |c k i|) Filter.atTop (nhds 0) := by
    simpa only [abs_zero] using (hc i hi).abs
  have hsum : Filter.Tendsto (fun k => ∑ i ∈ S, |c k i|)
      Filter.atTop (nhds (∑ i ∈ S, (0 : ℝ))) :=
    tendsto_finset_sum S (fun i hi => hone i hi)
  simpa using hsum
