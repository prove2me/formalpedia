-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_nonnegative_random_poly_primitive_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T16:08:15.467695+00:00
-- url     : https://prove2.me/submissions/9400f320-227f-47c5-919e-fb23c93cd55b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators
open AvramDividend.Classical

/-! An integrated exponential polynomial along any a.e. nonnegative
random residual is Bochner integrable on a probability space. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hMeas : Measurable R)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ R ω)
    (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) :
    Integrable (fun ω => (∫ r in (0 : ℝ)..R ω,
      Polynomial.eval (Real.exp (-r)) p)) P := by
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
      Integrable (fun ω => (p.coeff k / (k : ℝ)) *
        (1 - Real.exp (-((k : ℝ) * R ω)))) P := by
    exact ((integrable_const (1 : ℝ)).sub (hExpI k)).const_mul _
  have hSumI : Integrable (fun ω =>
      ∑ k ∈ p.support.erase 0,
        (p.coeff k / (k : ℝ)) *
          (1 - Real.exp (-((k : ℝ) * R ω)))) P := by
    apply integrable_finset_sum
    intro k hk
    exact hTermI k
  have hEq (ω : Ω) :
      (∫ r in (0 : ℝ)..R ω, Polynomial.eval (Real.exp (-r)) p) =
        ∑ k ∈ p.support.erase 0,
          (p.coeff k / (k : ℝ)) *
          (1 - Real.exp (-((k : ℝ) * R ω))) := by
    rw [avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits p hp (R ω)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_neg]
    ring
  exact hSumI.congr (Filter.Eventually.of_forall (fun ω => (hEq ω).symm))
