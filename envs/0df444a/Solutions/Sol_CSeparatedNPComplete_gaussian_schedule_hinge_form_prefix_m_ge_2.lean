-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_hinge_form_prefix_m_ge_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:51.021109+00:00
-- url     : https://prove2.me/submissions/f0eb429b-cef1-4ed5-ad8a-94d70067fcc7

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_snoc
public import Theorems.Thm_CSeparatedNPComplete_hinge_to_gaussian_schedule_last
public import Theorems.Thm_CSeparatedNPComplete_hinge_form_snoc


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : ℕ} (k : ℕ) {m c : ℝ}
    (a : Vec n) (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : is_vec_leq 0 a)
    (hsum : dot a 1 = m) :
    hinge_form c a (gaussian_schedule m (k + 1)) =
      c * (k : ℝ) * ((k : ℝ) + 1) / 2 - gaussian_schedule_hinge_correction a k := by
  induction k with
  | zero => simp [gaussian_schedule, hinge_form, hinge_against,
      gaussian_schedule_hinge_correction]
  | succ k ih =>
    rw [gaussian_schedule_snoc, hinge_form_snoc, ih,
      hinge_to_gaussian_schedule_last a hm hc ha hsum (Nat.succ_pos k)]
    simp only [gaussian_schedule_hinge_correction, Finset.sum_range_succ,
      Nat.cast_succ, Nat.succ_eq_add_one, Nat.add_sub_cancel]
    ring
end CSeparatedNPComplete
