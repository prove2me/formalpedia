-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_stopped_gaussian_energy_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:35:03.111519+00:00
-- url     : https://prove2.me/submissions/f5bbf85e-a01e-477e-8c2a-fca0dfb4293d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_energy_small_parameter_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Same-path right-continuous Gaussian stopped source rightstop_limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    Filter.Tendsto (fun ε : ℝ => (∫ ω,
      ((Real.exp (Real.sqrt ε *
          (X.X (τ ω + h) ω - X.X (τ ω) ω) -
          (h : ℝ) * X.ψ (Real.sqrt ε)) - 1) /
            Real.sqrt ε) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 ((h : ℝ) * X.σ ^ 2)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Y, hpath, hc, hσ, hνY⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hYν : Y.ν = 0 := by
    rw [hνY, hν]
  have hψ : ∀ ξ : ℝ, Y.ψ ξ = X.ψ ξ := by
    intro ξ
    simp only [SpectrallyNegativeLevy.ψ, hc, hσ, hνY]
  have hLimit :=
    avram_wave5_03a_source_stopped_gaussian_energy_small_parameter_limit
      Y hYν τ hτ T hbounded h
  simpa only [hpath, hψ, hσ] using hLimit
