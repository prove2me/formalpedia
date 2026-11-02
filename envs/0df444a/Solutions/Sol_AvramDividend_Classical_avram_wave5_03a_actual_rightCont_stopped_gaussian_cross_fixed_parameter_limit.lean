-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_cross_fixed_parameter_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:09:22.863139+00:00
-- url     : https://prove2.me/submissions/c440fe3c-3158-45a6-98b8-7719f68e7f73

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_quadratic_secant_right_limit

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Same original source stopped Gaussian cross covariance has correct fixed-parameter derivative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    Filter.Tendsto
      (fun η : ℝ =>
        (∫ ω,
          ((Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
              (h : ℝ) * X.ψ θ) - 1) / θ) *
          ((Real.exp (η * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
              (h : ℝ) * X.ψ η) - 1) / η) ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 ((h : ℝ) * X.σ ^ 2)) := by
  have hsec : Filter.Tendsto
      (fun η : ℝ =>
        (Real.exp (((h : ℝ) * X.σ ^ 2 * θ) * η) - 1) / η)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((h : ℝ) * X.σ ^ 2 * θ)) := by
    simpa only [zero_mul, add_zero] using
      (avram_wave5_03a_exp_quadratic_secant_right_limit
        ((h : ℝ) * X.σ ^ 2 * θ) 0)
  have hscaled : Filter.Tendsto
      (fun η : ℝ => (1 / θ) *
        ((Real.exp (((h : ℝ) * X.σ ^ 2 * θ) * η) - 1) / η))
      (𝓝[>] (0 : ℝ)) (𝓝 ((h : ℝ) * X.σ ^ 2)) := by
    have hscaleEq : (1 / θ) * ((h : ℝ) * X.σ ^ 2 * θ) =
        (h : ℝ) * X.σ ^ 2 := by
      field_simp [ne_of_gt hθ] <;> ring
    simpa only [hscaleEq] using hsec.const_mul (1 / θ)
  refine hscaled.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hηpos : 0 < η := hη
  rw [avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
    X hν τ hτ T hbounded h θ η (le_of_lt hθ) (le_of_lt hηpos)]
  have hexp :
      (h : ℝ) * (X.σ ^ 2 * θ * η) =
        ((h : ℝ) * X.σ ^ 2 * θ) * η := by ring
  rw [hexp]
  field_simp [ne_of_gt hθ, ne_of_gt hηpos] <;> ring
