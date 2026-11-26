-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_separation_sum_diagonal_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:50.084574+00:00
-- url     : https://prove2.me/submissions/16acc228-4d31-460b-99a3-e4d9f40c3203

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_scaled_le
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_nonneg


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {m : ℝ} (hm : 2 ≤ m)
    {i j : ℕ} (hij : i ≤ j) :
    gaussian_schedule_separation_sum m i i ≤ gaussian_schedule_separation_sum m j j := by
  rcases hij.eq_or_lt with rfl | hij
  · rfl
  · have hn := gaussian_schedule_separation_sum_nonneg m i i
    have hs := gaussian_schedule_separation_sum_scaled_le hm hij
    nlinarith
end CSeparatedNPComplete
