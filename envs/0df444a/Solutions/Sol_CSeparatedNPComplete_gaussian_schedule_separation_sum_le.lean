-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_separation_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:17.774657+00:00
-- url     : https://prove2.me/submissions/1938c3b7-1b97-4bfc-83ae-0904c2cc9c6b

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution (m : ℝ) (i : ℕ) {k l : ℕ}
    (hkl : k ≤ l) :
    gaussian_schedule_separation_sum m i k ≤ gaussian_schedule_separation_sum m i l := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl)
    (fun _ _ _ => sq_nonneg _)
end CSeparatedNPComplete
