-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:35:35.610471+00:00
-- url     : https://prove2.me/submissions/a2b97b81-eac4-45bc-8378-af39a99ab6ef

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_centered_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Same-path right-continuous bounded stopping: source Gaussian quotient is L2 and centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    MemLp (fun ω => (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) - 1) / θ) 2 P ∧
      (∫ ω, (Real.exp (θ *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Y, hpath, hc, hσ, hνY⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hYν : Y.ν = 0 := by
    rw [hνY, hν]
  have hψ : Y.ψ θ = X.ψ θ := by
    simp only [SpectrallyNegativeLevy.ψ, hc, hσ, hνY]
  have hQuot :=
    avram_wave5_03a_source_stopped_gaussian_exponential_quotient_centered_L2
      Y hYν τ hτ T hbounded h θ hθ
  simpa only [hpath, hψ] using hQuot
