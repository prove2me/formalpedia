-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_original_rightCont_gaussian_quotient_two_sequence_L2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:11:11.383984+00:00
-- url     : https://prove2.me/submissions/d3aa3c05-b422-4731-af0e-a5cabb8f740a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_stopped_gaussian_quotient_two_sequence_L2_cauchy

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Same-path right-continuous stopped source L2 Cauchy for positive null sequences. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (θ η : ℕ → ℝ)
    (hθ : Filter.Tendsto θ atTop (𝓝[>] (0 : ℝ)))
    (hη : Filter.Tendsto η atTop (𝓝[>] (0 : ℝ))) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto (fun n : ℕ =>
      (∫ ω, (Z (θ n) ω - Z (η n) ω) ^ 2 ∂P))
      atTop (𝓝 (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Y, hpath, hc, hσ, hνY⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hYν : Y.ν = 0 := by
    rw [hνY, hν]
  have hψ : ∀ ξ : ℝ, Y.ψ ξ = X.ψ ξ := by
    intro ξ
    simp only [SpectrallyNegativeLevy.ψ, hc, hσ, hνY]
  have hLim :=
    avram_wave5_03a_original_stopped_gaussian_quotient_two_sequence_L2_cauchy
      Y hYν τ hτ T hbounded h θ η hθ hη
  simpa only [hpath, hψ] using hLim
