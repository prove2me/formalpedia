-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:43:27.939892+00:00
-- url     : https://prove2.me/submissions/9b6c66db-91d9-4b2d-a500-bdf5d6a505ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_indepIncrements_rightCont
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_integral_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact mean-one stopped source likelihood for the genuine right-continuous clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ) ∂P) = (1 : ℝ) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : SpectrallyNegativeLevy P 𝓕.rightCont :=
    { X := X.X
      c := X.c
      σ := X.σ
      ν := X.ν
      isProbability := X.isProbability
      σ_nonneg := X.σ_nonneg
      ν_Ici := X.ν_Ici
      ν_integrable := X.ν_integrable
      X_zero := X.X_zero
      rightCont := X.rightCont
      leftLim := X.leftLim
      noPosJumps := X.noPosJumps
      adapted := by
        intro t
        exact (X.adapted t).mono (𝓕.le_rightCont t) le_rfl
      indepIncrements := by
        intro s t hst
        exact levy_indepIncrements_rightCont X s t hst
      stationaryIncrements := X.stationaryIncrements
      laplace := X.laplace }
  have hPath : Y.X = X.X := rfl
  have hPsi : Y.ψ θ = X.ψ θ := rfl
  have hStopped := esscher_bounded_stop_likelihood_integral_one
    Y θ hθ τ hstop H hbound (H + 1) le_rfl
  simpa only [hPath, hPsi] using hStopped
