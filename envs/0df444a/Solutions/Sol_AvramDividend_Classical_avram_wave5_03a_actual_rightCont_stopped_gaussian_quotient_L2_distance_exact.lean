-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_quotient_L2_distance_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:24:56.784211+00:00
-- url     : https://prove2.me/submissions/d66f5878-7851-4ad8-8b0c-494d1177c840

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Exact same-original-path right-continuous-stopped Gaussian source L2 distance kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    (∫ ω, (Z θ ω - Z η ω) ^ 2 ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) / θ ^ 2 +
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * η ^ 2)) - 1) / η ^ 2 -
      2 * ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η)) := by
  obtain ⟨Y, hpaths, hc, hsigma, hmeasure⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hνY : Y.ν = 0 := hmeasure.trans hν
  have hψθ : Y.ψ θ = X.ψ θ := by
    simp only [SpectrallyNegativeLevy.ψ, hc, hsigma, hmeasure]
  have hψη : Y.ψ η = X.ψ η := by
    simp only [SpectrallyNegativeLevy.ψ, hc, hsigma, hmeasure]
  have hcore :=
    avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact
      Y hνY τ hτ T hbounded h θ η hθ hη
  simpa only [hpaths, hsigma, hψθ, hψη] using hcore
