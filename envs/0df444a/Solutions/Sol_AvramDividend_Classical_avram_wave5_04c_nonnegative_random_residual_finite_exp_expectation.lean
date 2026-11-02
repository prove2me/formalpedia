-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_nonnegative_random_residual_finite_exp_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:34:30.018074+00:00
-- url     : https://prove2.me/submissions/02880e01-f307-4084-b2fb-ec45c404d417

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

/-! Expectation of a finite signed exponential-deficit family at an arbitrary
a.e. nonnegative measurable residual on the original probability space.
This is the finite-sum Bochner interchange needed by the BV generator bridge. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hMeas : Measurable R)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ R ω)
    (s : Finset ℕ) (coeff : ℕ → ℝ) :
    (∫ ω, ∑ k ∈ s, coeff k *
      (1 - Real.exp (-((k : ℝ) * R ω))) ∂P) =
    ∑ k ∈ s, coeff k *
      (1 - (∫ ω, Real.exp (-((k : ℝ) * R ω)) ∂P)) := by
  have hExpI (k : ℕ) :
      Integrable (fun ω => Real.exp (-((k : ℝ) * R ω))) P := by
    have hm : Measurable (fun ω => Real.exp (-((k : ℝ) * R ω))) := by
      fun_prop
    have hb : ∀ᵐ ω ∂P,
        ‖Real.exp (-((k : ℝ) * R ω))‖ ≤ 1 := by
      filter_upwards [hNonneg] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (mul_nonneg (by positivity) hω)
    exact (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable hb
  have hTermI (k : ℕ) :
      Integrable (fun ω => coeff k *
        (1 - Real.exp (-((k : ℝ) * R ω)))) P := by
    exact ((integrable_const (1 : ℝ)).sub (hExpI k)).const_mul _
  calc
    (∫ ω, ∑ k ∈ s, coeff k *
      (1 - Real.exp (-((k : ℝ) * R ω))) ∂P) =
        ∑ k ∈ s, (∫ ω, coeff k *
          (1 - Real.exp (-((k : ℝ) * R ω))) ∂P) := by
            apply integral_finset_sum s
            intro k hk
            exact hTermI k
    _ = ∑ k ∈ s, coeff k *
        (1 - (∫ ω, Real.exp (-((k : ℝ) * R ω)) ∂P)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [integral_const_mul]
          rw [integral_sub (integrable_const (1 : ℝ)) (hExpI k)]
          simp
