-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:34:21.644631+00:00
-- url     : https://prove2.me/submissions/da98d14e-1a64-4ac6-a235-6e259f07d1ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Same-path right-continuous Gaussian stopped source rightstop_cross. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    (∫ ω, ((Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) - 1) / θ) *
      ((Real.exp (η *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ η) - 1) / η) ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Y, hpath, hc, hσ, hνY⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hYν : Y.ν = 0 := by
    rw [hνY, hν]
  have hψθ : Y.ψ θ = X.ψ θ := by
    simp only [SpectrallyNegativeLevy.ψ, hc, hσ, hνY]
  have hψη : Y.ψ η = X.ψ η := by
    simp only [SpectrallyNegativeLevy.ψ, hc, hσ, hνY]
  have hCross :=
    avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy
      Y hYν τ hτ T hbounded h θ η hθ hη
  simpa only [hpath, hψθ, hψη, hσ] using hCross
