-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_sigma_dot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:47:16.683903+00:00
-- url     : https://prove2.me/submissions/a076b9d1-aa25-47aa-96b8-d96c859dc80e

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
theorem _root_.solution {n : ℕ} (m : ℝ) (a : Vec n) {j : ℕ}
    (hj : j ≠ 0) :
    dot a (gaussian_schedule_sigma m j) =
      gaussian_schedule_separation_sum m j j * (m * dot a (canon_e (j - 1)) + dot a 1) := by
  simp only [gaussian_schedule_sigma, if_neg hj, dot, mul_add, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.one_apply]
  ring
end CSeparatedNPComplete
