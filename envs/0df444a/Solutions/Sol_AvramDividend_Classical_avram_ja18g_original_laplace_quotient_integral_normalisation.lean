-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_laplace_quotient_integral_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:36:52.188772+00:00
-- url     : https://prove2.me/submissions/369cc40e-298f-4dc4-8d6b-52713a2954a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Normalise the original Laplace moment by the probability mass one and
    move the scalar quotient through the finite physical integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (θ : ℝ) (hθ : 0 < θ) :
    ((∫ ω, Real.exp (θ * X.X t ω) ∂P) - 1) / θ =
      ∫ ω, (Real.exp (θ * X.X t ω) - 1) / θ ∂P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hCent : Integrable
      (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) P :=
    levy_compensated_exponential_integrable X t θ hθ.le
  have hExp : Integrable (fun ω => Real.exp (θ * X.X t ω)) P := by
    have heq : (fun ω => Real.exp (θ * X.X t ω)) =
        (fun ω => Real.exp ((t : ℝ) * X.ψ θ) *
          Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) := by
      funext ω
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hCent.const_mul _
  have hOne : (∫ _ : Ω, (1 : ℝ) ∂P) = 1 := by simp
  calc
    ((∫ ω, Real.exp (θ * X.X t ω) ∂P) - 1) / θ =
        ((∫ ω, Real.exp (θ * X.X t ω) ∂P) -
          (∫ _ : Ω, (1 : ℝ) ∂P)) / θ := by rw [hOne]
    _ = (∫ ω, Real.exp (θ * X.X t ω) - 1 ∂P) / θ := by
      rw [integral_sub hExp (integrable_const (1 : ℝ))]
    _ = ∫ ω, (Real.exp (θ * X.X t ω) - 1) / θ ∂P := by
      rw [integral_div]
