-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_ioc_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:40:01.993212+00:00
-- url     : https://prove2.me/submissions/e6d56c3e-cacd-445e-b65f-d802d0c238a2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

/-- Distinct uniform strict-left/right-closed source time cells are disjoint. -/
theorem solution
    (m : ℕ) (δ : ℝ≥0) :
    ∀ i j : Fin m, i ≠ j →
      Disjoint
        (Ioc ((i.val : ℝ≥0) * δ) (((i.val + 1 : ℕ) : ℝ≥0) * δ))
        (Ioc ((j.val : ℝ≥0) * δ) (((j.val + 1 : ℕ) : ℝ≥0) * δ)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · have hsucc : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hlt
    have hcast : ((i.val + 1 : ℕ) : ℝ≥0) ≤ (j.val : ℝ≥0) := by
      exact_mod_cast hsucc
    have hmul : (((i.val + 1 : ℕ) : ℝ≥0) * δ) ≤
        (j.val : ℝ≥0) * δ := mul_le_mul_of_nonneg_right hcast (by positivity)
    exact (not_lt_of_ge (le_trans hxi.2 hmul)) hxj.1
  · exact hij (Fin.ext heq)
  · have hsucc : j.val + 1 ≤ i.val := Nat.succ_le_of_lt hgt
    have hcast : ((j.val + 1 : ℕ) : ℝ≥0) ≤ (i.val : ℝ≥0) := by
      exact_mod_cast hsucc
    have hmul : (((j.val + 1 : ℕ) : ℝ≥0) * δ) ≤
        (i.val : ℝ≥0) * δ := mul_le_mul_of_nonneg_right hcast (by positivity)
    exact (not_lt_of_ge (le_trans hxj.2 hmul)) hxi.1
