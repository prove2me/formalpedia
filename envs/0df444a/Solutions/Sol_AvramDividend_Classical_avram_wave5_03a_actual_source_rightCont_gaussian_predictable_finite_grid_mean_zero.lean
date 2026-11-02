-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_gaussian_predictable_finite_grid_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:23:45.276795+00:00
-- url     : https://prove2.me/submissions/394db902-0219-4d9f-87a1-674683ed0963

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_gaussian_finite_grid_predictable_exponential_quotient_integral_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original source, right-continuous filtration: predictable finite Gaussian exponential grids are centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (S : Finset ι)
    (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (K : ι → ℝ)
    (hBound : ∀ i ∈ S, ∀ ω, ‖H i ω‖ ≤ K i)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, ∑ i ∈ S, H i ω *
      ((Real.exp (θ * (X.X (t i) ω - X.X (s i) ω) -
        ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) - 1) / θ) ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Y, hpath, hc, hσ, hνY⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hYν : Y.ν = 0 := by
    rw [hνY, hν]
  have hψ : Y.ψ θ = X.ψ θ := by
    simp only [SpectrallyNegativeLevy.ψ, hc, hσ, hνY]
  have hGrid :=
    avram_wave5_03a_original_gaussian_finite_grid_predictable_exponential_quotient_integral_zero
      Y hYν S s t hst H hH K hBound θ hθ
  simpa only [hpath, hψ] using hGrid
