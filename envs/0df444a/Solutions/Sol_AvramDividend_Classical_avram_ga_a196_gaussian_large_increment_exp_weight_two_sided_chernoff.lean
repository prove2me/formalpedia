-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a196_gaussian_large_increment_exp_weight_two_sided_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:49:04.622133+00:00
-- url     : https://prove2.me/submissions/44fca764-b9f6-4eda-a3b8-12165c481ecd

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- Two-sided Chernoff domination for a source Gaussian exponential observable
restricted to large centred physical increments. -/
theorem solution
    (θ r η z : ℝ) (hr : 0 ≤ r) (hη : 0 ≤ η) :
    (if η ≤ |z| then Real.exp (θ * z) else 0) ≤
      Real.exp (-r * η) *
        (Real.exp ((θ + r) * z) + Real.exp ((θ - r) * z)) := by
  by_cases ht : η ≤ |z|
  · simp only [if_pos ht]
    by_cases hz : 0 ≤ z
    · have hlarge : η ≤ z := by simpa [abs_of_nonneg hz] using ht
      have hlin : θ * z ≤ -r * η + (θ + r) * z := by
        nlinarith [mul_nonneg hr (sub_nonneg.mpr hlarge)]
      have hExp : Real.exp (θ * z) ≤
          Real.exp (-r * η) * Real.exp ((θ + r) * z) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr hlin
      calc
        Real.exp (θ * z) ≤ Real.exp (-r * η) *
            Real.exp ((θ + r) * z) := hExp
        _ ≤ Real.exp (-r * η) *
            (Real.exp ((θ + r) * z) + Real.exp ((θ - r) * z)) := by
          apply mul_le_mul_of_nonneg_left
          · exact le_add_of_nonneg_right (le_of_lt (Real.exp_pos _))
          · exact le_of_lt (Real.exp_pos _)
    · have hneg : z ≤ 0 := le_of_not_ge hz
      have hlarge : η ≤ -z := by simpa [abs_of_nonpos hneg] using ht
      have hlin : θ * z ≤ -r * η + (θ - r) * z := by
        nlinarith [mul_nonneg hr (sub_nonneg.mpr hlarge)]
      have hExp : Real.exp (θ * z) ≤
          Real.exp (-r * η) * Real.exp ((θ - r) * z) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr hlin
      calc
        Real.exp (θ * z) ≤ Real.exp (-r * η) *
            Real.exp ((θ - r) * z) := hExp
        _ ≤ Real.exp (-r * η) *
            (Real.exp ((θ + r) * z) + Real.exp ((θ - r) * z)) := by
          apply mul_le_mul_of_nonneg_left
          · exact le_add_of_nonneg_left (le_of_lt (Real.exp_pos _))
          · exact le_of_lt (Real.exp_pos _)
  · simp only [if_neg ht]
    positivity
