-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_pair_hinge_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:33.398294+00:00
-- url     : https://prove2.me/submissions/38264de5-ad35-433a-814a-217fa4ed1796

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_sigma_dot
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_mu_distance
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_sigma_dot_positive_all
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_later_covariance
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_term_le_sum
public import Theorems.Thm_CSeparatedNPComplete_dot_canon_e_nonneg
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_nonneg


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : ℕ} {m c : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m)
    {i j : ℕ} (hij : i < j) :
    gaussian_pair_hinge c a (gaussian_schedule_class m i) (gaussian_schedule_class m j) =
      c - (m ^ i - m ^ j) ^ 2 * m / dot a (gaussian_schedule_sigma m j) := by
  have hord := gaussian_schedule_later_covariance a hm ha hsum hij
  have hpos := gaussian_schedule_sigma_dot_positive_all a hm ha hsum j
  have hterm := gaussian_schedule_separation_term_le_sum m hij
  have hej := dot_canon_e_nonneg a (j - 1) ha
  have hj0 := gaussian_schedule_separation_sum_nonneg m j j
  have hm0 : 0 ≤ m := by linarith
  have hbound : (m ^ i - m ^ j) ^ 2 * m ≤ dot a (gaussian_schedule_sigma m j) := by
    rw [gaussian_schedule_sigma_dot m a (by omega), hsum]
    calc
      _ ≤ gaussian_schedule_separation_sum m j j * m :=
        mul_le_mul_of_nonneg_right hterm hm0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) hj0
  have hratio : (m ^ i - m ^ j) ^ 2 * m / dot a (gaussian_schedule_sigma m j) ≤ 1 :=
    (div_le_one hpos).mpr hbound
  unfold gaussian_pair_hinge gaussian_pair_stats gaussian_schedule_class
  simp only [gaussian_schedule_mu_distance, hsum, max_eq_right hord]
  exact max_eq_right (by linarith)
end CSeparatedNPComplete
