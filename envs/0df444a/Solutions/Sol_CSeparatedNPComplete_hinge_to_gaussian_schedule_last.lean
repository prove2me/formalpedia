-- Prove2me | solution 1 for CSeparatedNPComplete.hinge_to_gaussian_schedule_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:11.833052+00:00
-- url     : https://prove2.me/submissions/6cf3ae9f-742b-4db9-b4de-34a28b26cbb0

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_ge_1
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_sigma_dot
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_pair_hinge_before
public import Theorems.Thm_CSeparatedNPComplete_dot_canon_e_nonneg


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : ℕ} {m c : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m)
    {j : ℕ} (hj : 0 < j) :
    hinge_to c a (gaussian_schedule m j) (gaussian_schedule_class m j) =
      c * (j : ℝ) - (1 + dot a (canon_e (j - 1)))⁻¹ := by
  have hspos : 0 < gaussian_schedule_separation_sum m j j :=
    lt_of_lt_of_le (by norm_num) (gaussian_schedule_separation_sum_ge_1 hm hj)
  have he := dot_canon_e_nonneg a (j - 1) ha
  have hmne : m ≠ 0 := by linarith
  have hene : 1 + dot a (canon_e (j - 1)) ≠ 0 := by linarith
  have hratio : gaussian_schedule_separation_sum m j j * m /
      dot a (gaussian_schedule_sigma m j) = (1 + dot a (canon_e (j - 1)))⁻¹ := by
    rw [gaussian_schedule_sigma_dot m a (Nat.ne_of_gt hj), hsum]
    have hfactor : m * dot a (canon_e (j - 1)) + m = m * (1 + dot a (canon_e (j - 1))) := by ring
    rw [hfactor]
    field_simp [hspos.ne', hmne, hene]
  have hsquares : (∑ i ∈ Finset.range j, (m ^ i - m ^ j) ^ 2) =
      gaussian_schedule_separation_sum m j j := by
    unfold gaussian_schedule_separation_sum
    apply Finset.sum_congr rfl
    intro i _
    exact sub_sq_comm _ _
  unfold hinge_to gaussian_schedule
  rw [List.map_map, ← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, Function.comp_apply]
  calc
    _ = ∑ i ∈ Finset.range j,
        (c - (m ^ i - m ^ j) ^ 2 * m / dot a (gaussian_schedule_sigma m j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact gaussian_schedule_pair_hinge_before a hm hc ha hsum (Finset.mem_range.mp hi)
    _ = c * (j : ℝ) - gaussian_schedule_separation_sum m j j * m /
        dot a (gaussian_schedule_sigma m j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.sum_div, ← Finset.sum_mul, hsquares]
      ring
    _ = _ := by rw [hratio]
end CSeparatedNPComplete
