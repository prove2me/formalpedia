-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_mu_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:31.477046+00:00
-- url     : https://prove2.me/submissions/200df80e-f7be-4ad1-8e81-35e4609b06c6

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
theorem _root_.solution {n : ℕ} (a : Vec n) (m : ℝ) (i j : ℕ) :
    dot a (sqVec (gaussian_schedule_mu m i - gaussian_schedule_mu m j)) =
      (m ^ i - m ^ j) ^ 2 * dot a 1 := by
  simp only [dot, sqVec, gaussian_schedule_mu, Pi.sub_apply, Pi.one_apply,
    mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring
end CSeparatedNPComplete
