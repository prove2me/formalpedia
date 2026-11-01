-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_intervalMass_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:32:52.459288+00:00
-- url     : https://prove2.me/submissions/3a776368-48d1-42fa-b345-39b0dc4d2f3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- A genuine source-Lévy stochastic budget for the full Stieltjes masses on
half-open payment cells, retaining diffuse and right-atomic dividend mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫ ω, θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal ∂P) ≤
    (∫ ω, Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) := by
  have hcell (ω : Ω) (i : ℕ) :
      (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal =
        rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω := by
    rw [dividendMeasure_Ioc_rightLimit D hD ω (u i) (u (i + 1))]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr
      (avram_wave3_03_dividendStrategy_rightLimit_monotone
        D hD ω (hu (Nat.le_succ i))))
  calc
    (∫ ω, θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal ∂P) =
      (∫ ω, θ * ∑ i ∈ Finset.range n,
        Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcell ω i]
    _ ≤ _ := (avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
      X D hD θ hθ u hu n).2