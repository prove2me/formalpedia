-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_separation_term_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:37.839973+00:00
-- url     : https://prove2.me/submissions/e3280a7a-8e9a-4a05-9327-11165335d075

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
theorem _root_.solution (m : ℝ) {i j : ℕ} (hij : i < j) :
    (m ^ i - m ^ j) ^ 2 ≤ gaussian_schedule_separation_sum m j j := by
  rw [sub_sq_comm]
  unfold gaussian_schedule_separation_sum
  exact Finset.single_le_sum (fun r _ => sq_nonneg (m ^ j - m ^ r))
    (Finset.mem_range.mpr hij)
end CSeparatedNPComplete
