-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:43.402162+00:00
-- url     : https://prove2.me/submissions/6dec9f69-c9f3-4dd4-a57a-4f61df18565d

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
theorem _root_.solution {n : ℕ} (m : ℝ) (k : ℕ) :
    gaussian_schedule (n := n) m (k + 1) =
      gaussian_schedule m k ++ [gaussian_schedule_class m k] := by
  simp [gaussian_schedule, List.range_succ]
end CSeparatedNPComplete
