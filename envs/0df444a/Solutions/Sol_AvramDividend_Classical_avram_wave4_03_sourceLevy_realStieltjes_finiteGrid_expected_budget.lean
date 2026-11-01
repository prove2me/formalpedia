-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_realStieltjes_finiteGrid_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:00:41.082709+00:00
-- url     : https://prove2.me/submissions/90737a58-cd1b-4f53-adb0-fa973fda6e80

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_realStieltjes_cellStep_integral_eq_gridMass
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_intervalMass_expected_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Genuine same-filtration original Lévy expected full-Stieltjes finite-step
dividend budget, with the inner time integral taken against dividendMeasure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (n : ℕ) :
    (∫ ω, ∫ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        θ * Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    (∫ ω, Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) := by
  calc
    (∫ ω, ∫ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        θ * Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω))
      else 0 ∂dividendMeasure D ω ∂P) =
      (∫ ω, ∑ i ∈ Finset.range n,
        (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal *
        (θ * Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact avram_wave4_03_sourceLevy_realStieltjes_cellStep_integral_eq_gridMass
        X D θ u n ω hD
    _ = (∫ ω, θ * ∑ i ∈ Finset.range n,
        Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
        (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := avram_wave4_03_sourceLevy_finiteGrid_intervalMass_expected_budget
      X D hD θ hθ u hu n