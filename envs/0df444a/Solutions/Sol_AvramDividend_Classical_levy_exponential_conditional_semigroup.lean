-- Prove2me | solution 1 for AvramDividend.Classical.levy_exponential_conditional_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:47:02.279086+00:00
-- url     : https://prove2.me/submissions/597ac53c-044f-478f-8bc2-75079c3296f4

import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_exponential_condExp_factorization

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    P[(fun ω => Real.exp (θ * X.X t ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => Real.exp (θ * X.X s ω) *
        (∫ η, Real.exp (θ * X.X (t - s) η) ∂P)) := by
  have hF : Measurable (fun z : ℝ => Real.exp (θ * z)) :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).measurable
  have hPast : StronglyMeasurable[𝓕 s]
      (fun ω => Real.exp (θ * X.X s ω)) :=
    (hF.comp (X.adapted s)).stronglyMeasurable
  have hTotal :
      Integrable (fun ω => Real.exp (θ * X.X t ω)) P :=
    (X.laplace t θ hθ).1
  have hDet :
      Integrable (fun ω => Real.exp (θ * X.X (t - s) ω)) P :=
    (X.laplace (t - s) θ hθ).1
  have hIdent :
      IdentDistrib
        (fun ω => Real.exp (θ * (X.X t ω - X.X s ω)))
        (fun ω => Real.exp (θ * X.X (t - s) ω)) P P := by
    simpa only [Function.comp_def] using
      (X.stationaryIncrements s t hst).comp hF
  have hIncrement :
      Integrable (fun ω =>
        Real.exp (θ * (X.X t ω - X.X s ω))) P :=
    hIdent.integrable_iff.mpr hDet
  exact levy_exponential_condExp_factorization
    X s t hst θ hPast hTotal hIncrement hDet
