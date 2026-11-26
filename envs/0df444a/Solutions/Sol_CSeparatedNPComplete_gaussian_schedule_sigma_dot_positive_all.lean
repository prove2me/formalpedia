-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_sigma_dot_positive_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:42.992798+00:00
-- url     : https://prove2.me/submissions/9b353758-e1b7-42db-bc4f-693164aa0f59

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_ge_1
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_sigma_dot
public import Theorems.Thm_CSeparatedNPComplete_dot_canon_e_nonneg


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : ℕ} {m : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m) (j : ℕ) :
    0 < dot a (gaussian_schedule_sigma m j) := by
  by_cases hj : j = 0
  · simp only [gaussian_schedule_sigma, if_pos hj, hsum]
    linarith
  · rw [gaussian_schedule_sigma_dot m a hj, hsum]
    have he := dot_canon_e_nonneg a (j - 1) ha
    have hs := gaussian_schedule_separation_sum_ge_1 hm (Nat.pos_of_ne_zero hj)
    apply mul_pos (by linarith)
    nlinarith
end CSeparatedNPComplete
