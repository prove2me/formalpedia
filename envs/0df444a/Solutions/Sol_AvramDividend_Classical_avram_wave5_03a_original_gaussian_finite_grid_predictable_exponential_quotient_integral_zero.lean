-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_original_gaussian_finite_grid_predictable_exponential_quotient_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:18:10.981026+00:00
-- url     : https://prove2.me/submissions/b63edd26-be21-45c2-9f8d-dd1aaccd28f1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original-filtration predictable simple exponential-Gaussian integral has zero expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (S : Finset ι)
    (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓕 (s i)] (H i))
    (K : ι → ℝ)
    (hBound : ∀ i ∈ S, ∀ ω, ‖H i ω‖ ≤ K i)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, ∑ i ∈ S, H i ω *
      ((Real.exp (θ * (X.X (t i) ω - X.X (s i) ω) -
        ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) - 1) / θ) ∂P) = 0 := by
  classical
  let φ : ι → ℝ → ℝ :=
    fun i x => (Real.exp (θ * x -
      ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) - 1) / θ
  have hφ : ∀ i ∈ S, Measurable (φ i) := by
    intro i hi
    dsimp [φ]
    fun_prop
  have hInt : ∀ i ∈ S,
      Integrable (fun ω => φ i (X.X (t i - s i) ω)) P := by
    intro i hi
    have he := levy_compensated_exponential_integrable
      X (t i - s i) θ hθ
    have hsub : Integrable (fun ω => Real.exp
        (θ * X.X (t i - s i) ω -
          ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) - 1) P :=
      he.sub (integrable_const (1 : ℝ))
    have hscaled := hsub.mul_const θ⁻¹
    simpa only [φ, div_eq_mul_inv] using hscaled
  have hmean : ∀ i ∈ S,
      (∫ ω, φ i (X.X (t i - s i) ω) ∂P) = 0 := by
    intro i hi
    have he := levy_compensated_exponential_integrable
      X (t i - s i) θ hθ
    change (∫ ω, (Real.exp
      (θ * X.X (t i - s i) ω -
        ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) - 1) / θ ∂P) = 0
    calc
      _ = (∫ ω, (Real.exp
          (θ * X.X (t i - s i) ω -
            ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) - 1) ∂P) / θ := by
        simp only [div_eq_mul_inv, integral_mul_const]
      _ = ((∫ ω, Real.exp
          (θ * X.X (t i - s i) ω -
            ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) ∂P) -
          ∫ ω, (1 : ℝ) ∂P) / θ := by
        rw [integral_sub he (integrable_const (1 : ℝ))]
      _ = 0 := by
        rw [levy_compensated_exponential_expectation_one X (t i - s i) θ hθ]
        simp
  exact avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero
    X S s t hst φ hφ H hH K hBound hInt hmean
