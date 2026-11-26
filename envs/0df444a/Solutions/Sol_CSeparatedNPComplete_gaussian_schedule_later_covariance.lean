-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_later_covariance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:50.691517+00:00
-- url     : https://prove2.me/submissions/ae0df639-886a-4ee8-9a3c-2b6dc5489304

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_ge_1
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_scaled_le
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_sigma_dot
public import Theorems.Thm_CSeparatedNPComplete_dot_canon_e_le_dot_one
public import Theorems.Thm_CSeparatedNPComplete_dot_canon_e_nonneg
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_nonneg


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : ℕ} {m : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m)
    {i j : ℕ} (hij : i < j) :
    dot a (gaussian_schedule_sigma m i) ≤ dot a (gaussian_schedule_sigma m j) := by
  have hj : j ≠ 0 := by omega
  have hm0 : 0 ≤ m := by linarith
  have hj0 := gaussian_schedule_separation_sum_nonneg m j j
  have hej := dot_canon_e_nonneg a (j - 1) ha
  rw [gaussian_schedule_sigma_dot m a hj, hsum]
  by_cases hi : i = 0
  · simp only [gaussian_schedule_sigma, if_pos hi, hsum]
    have hs := gaussian_schedule_separation_sum_ge_1 hm (Nat.pos_of_ne_zero hj)
    calc
      m ≤ gaussian_schedule_separation_sum m j j * m := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) hj0
  · rw [gaussian_schedule_sigma_dot m a hi, hsum]
    have hi0 := gaussian_schedule_separation_sum_nonneg m i i
    have hei := dot_canon_e_le_dot_one a (i - 1) ha
    rw [hsum] at hei
    have hscaled := gaussian_schedule_separation_sum_scaled_le hm hij
    calc
      _ ≤ gaussian_schedule_separation_sum m i i * (m * (m + 1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hi0
      _ = m * ((m + 1) * gaussian_schedule_separation_sum m i i) := by ring
      _ ≤ m * gaussian_schedule_separation_sum m j j :=
        mul_le_mul_of_nonneg_left hscaled hm0
      _ ≤ gaussian_schedule_separation_sum m j j * (m * dot a (canon_e (j - 1)) + m) := by
        rw [mul_comm m]
        exact mul_le_mul_of_nonneg_left (by nlinarith) hj0
end CSeparatedNPComplete
