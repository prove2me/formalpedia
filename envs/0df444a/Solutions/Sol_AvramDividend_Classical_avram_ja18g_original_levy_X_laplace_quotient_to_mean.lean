-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_levy_X_laplace_quotient_to_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:23:55.547739+00:00
-- url     : https://prove2.me/submissions/a21acd26-671d-40a6-a03b-ab3734d1361c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_scalar_exponential_quotient_right_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_laplace_quotient_integrable_dominator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Differentiate the original physical exponential moment at zero from the
scalar right slope and an original-space integrable dominating function. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      Filter.Tendsto
        (fun θ : ℝ =>
          ((∫ ω, Real.exp (θ * X.X t ω) ∂P) - 1) / θ)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (∫ ω, X.X t ω ∂P)) := by
  intro t
  let F : ℝ → Ω → ℝ := fun θ ω =>
    (Real.exp (θ * X.X t ω) - 1) / θ
  obtain ⟨bound, hBoundInt, hMeas, hBound, hNormal⟩ :=
    avram_ja18g_original_laplace_quotient_integrable_dominator
      X hX hFinite t
  have hPoint : ∀ᵐ ω ∂P,
      Tendsto (fun θ : ℝ => F θ ω)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (X.X t ω)) := by
    filter_upwards [] with ω
    exact avram_ja18g_scalar_exponential_quotient_right_tendsto (X.X t ω)
  have hIntegral :=
    tendsto_integral_filter_of_dominated_convergence
      bound hMeas hBound hBoundInt hPoint
  exact hIntegral.congr' (hNormal.mono fun θ hθ => hθ.symm)
