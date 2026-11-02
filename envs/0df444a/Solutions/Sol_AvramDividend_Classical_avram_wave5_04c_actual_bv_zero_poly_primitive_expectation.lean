-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_poly_primitive_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:37:44.5321+00:00
-- url     : https://prove2.me/submissions/626bb904-3dce-4321-9b2d-f1ded2bd4857

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_nonnegative_random_residual_finite_exp_expectation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-! Exact original-process expectation interchange for the primitive of
a zero-constant polynomial, at every nonnegative Lévy time. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0)
    (t : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..((t : ℝ) * X.drift - X.X t ω),
      Polynomial.eval (Real.exp (-r)) p) ∂P) =
      ∑ k ∈ p.support.erase 0, (p.coeff k / (k : ℝ)) *
        (1 - (∫ ω, Real.exp (-((k : ℝ) *
          ((t : ℝ) * X.drift - X.X t ω))) ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let R : Ω → ℝ := fun ω => (t : ℝ) * X.drift - X.X t ω
  have hMeas : Measurable R :=
    measurable_const.sub ((X.adapted t).mono (𝓕.le _) le_rfl)
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ R ω := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hm
    have h0 := hm (show (0 : ℝ≥0) ≤ t from bot_le)
    simpa [R, X.X_zero] using h0
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
  calc
    (∫ ω, (∫ r in (0 : ℝ)..R ω,
      Polynomial.eval (Real.exp (-r)) p) ∂P) =
        (∫ ω, ∑ k ∈ p.support.erase 0,
          (p.coeff k / (k : ℝ)) *
          (1 - Real.exp (-((k : ℝ) * R ω))) ∂P) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hEq
    _ = ∑ k ∈ p.support.erase 0,
        (p.coeff k / (k : ℝ)) *
        (1 - (∫ ω, Real.exp (-((k : ℝ) * R ω)) ∂P)) :=
          avram_wave5_04c_nonnegative_random_residual_finite_exp_expectation
            R hMeas hNonneg (p.support.erase 0)
            (fun k => p.coeff k / (k : ℝ))
