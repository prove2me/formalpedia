-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18p2a_original_standing_jensen_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:59:07.366507+00:00
-- url     : https://prove2.me/submissions/a2ae6ffb-e2c1-4ba0-a2c6-e85b8f8143af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Jensen's inequality for the original one-time marginal and its Levy exponential identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      θ * (∫ ω, X.X 1 ω ∂P) ≤
        laplaceExponent X.c X.σ X.ν θ := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro θ hθ _hθOne
  have hXInt : Integrable (X.X 1) P := hX.2.1
  have hScaled : Integrable (fun ω => θ * X.X 1 ω) P :=
    hXInt.const_mul θ
  have hExp : Integrable
      (fun ω => Real.exp (θ * X.X 1 ω)) P :=
    (X.laplace 1 θ hθ.le).1
  have hConvex : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
  have hJensen :
      Real.exp (∫ ω, θ * X.X 1 ω ∂P) ≤
      ∫ ω, Real.exp (θ * X.X 1 ω) ∂P := by
    simpa only [Function.comp_def] using
      (hConvex.map_integral_le Real.continuous_exp.continuousOn
        isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
        hScaled (by simpa only [Function.comp_def] using hExp))
  have hLaplace :
      (∫ ω, Real.exp (θ * X.X 1 ω) ∂P) =
        Real.exp (laplaceExponent X.c X.σ X.ν θ) := by
    simpa using (X.laplace 1 θ hθ.le).2
  rw [hLaplace, integral_const_mul] at hJensen
  exact (Real.exp_le_exp.mp hJensen)
