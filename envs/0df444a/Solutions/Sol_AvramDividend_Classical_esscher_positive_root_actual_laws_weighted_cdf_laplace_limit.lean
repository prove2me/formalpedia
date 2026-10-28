-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_actual_laws_weighted_cdf_laplace_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T19:48:02.472241+00:00
-- url     : https://prove2.me/submissions/425e346f-12a4-45ba-8da9-10116c14d791

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_true_infimum_laws_cdf_converge
import Theorems.Thm_AvramDividend_Classical_esscher_probability_cdf_limits_imply_weighted_laplace_limits
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical ProbabilityTheory MeasureTheory Filter Set
open scoped ENNReal NNReal

/-- Actual exponentially observed Esscher infimum probability laws
    converge in exponentially weighted capital transforms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ β : ℝ, 0 < β → Tendsto
        (fun n : ℕ => (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * cdf (Measure.map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
  s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) ((P.prod (expMeasure (p n))).withDensity
  (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
    (φ * X.X (Real.toNNReal z.2) z.1 -
      (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) x ∂volume))
        atTop (nhds (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * cdf ν x ∂volume))) := by
  obtain ⟨ν, hν, hμ, hCDF, _⟩ :=
    esscher_positive_root_true_infimum_laws_cdf_converge
      X q φ hq hφ hroot p hp hpos
  let μ : ℕ → Measure ℝ := fun n => (Measure.map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
  s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) ((P.prod (expMeasure (p n))).withDensity
  (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
    (φ * X.X (Real.toNNReal z.2) z.1 -
      (Real.toNNReal z.2 : ℝ) * X.ψ φ)))))
  refine ⟨ν, hν, ?_⟩
  letI : IsProbabilityMeasure ν := hν
  intro β hβ
  exact esscher_probability_cdf_limits_imply_weighted_laplace_limits
    μ ν hμ hCDF β hβ
