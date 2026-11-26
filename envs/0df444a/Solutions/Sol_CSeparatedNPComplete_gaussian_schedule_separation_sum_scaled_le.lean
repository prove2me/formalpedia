-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_separation_sum_scaled_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:02.244003+00:00
-- url     : https://prove2.me/submissions/7376599c-45ed-46a7-880b-025c7409c6a7

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_term_scaled_le

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {m : ℝ} {i j : ℕ}
    (hm : 2 ≤ m) (hij : i < j) :
    (m + 1) * gaussian_schedule_separation_sum m i i ≤
      gaussian_schedule_separation_sum m j j := by
  unfold gaussian_schedule_separation_sum
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum (fun k hk => gaussian_schedule_separation_term_scaled_le
    hm (Finset.mem_range.mp hk) hij)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij.le)
      (fun _ _ _ => sq_nonneg _))
end CSeparatedNPComplete
