-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_separation_sum_ge_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:47:12.472997+00:00
-- url     : https://prove2.me/submissions/90ee9cb9-9436-4d9f-b60d-4c75a78f5c02

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
theorem _root_.solution {m : ℝ} {j : ℕ}
    (hm : 2 ≤ m) (hj : 0 < j) :
    1 ≤ gaussian_schedule_separation_sum m j j := by
  have hm1 : 1 ≤ m := by linarith
  have hp : m ≤ m ^ j := le_self_pow₀ hm1 (by omega)
  calc
    1 ≤ (m ^ j - m ^ 0) ^ 2 := by simp only [pow_zero]; nlinarith
    _ ≤ gaussian_schedule_separation_sum m j j := by
      unfold gaussian_schedule_separation_sum
      exact Finset.single_le_sum (fun r _ => sq_nonneg (m ^ j - m ^ r))
        (Finset.mem_range.mpr hj)
end CSeparatedNPComplete
