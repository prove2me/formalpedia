-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_perpetual_probability_support_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T20:07:29.390743+00:00
-- url     : https://prove2.me/submissions/e955813f-17e1-4740-b2e4-08c50e6aed32

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_infimum_finite_nonnegative_distribution
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- The genuine perpetual Esscher probability is supported on the nonnegative
    reflected infimum, and its CDF has the exact positive Laplace identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ν (Iio (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, ν (Iic x) =
        (⨅ t : ℝ≥0, ENNReal.ofReal
          (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
            (fun ω => Real.exp (φ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P))) ∧
      (∀ β : ℝ, 0 < β →
        (∫⁻ x : ℝ in Ioi 0,
     ENNReal.ofReal (Real.exp (-β * x)) * ν (Iic x)) =
          ENNReal.ofReal (1 / β) * (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν)) ∧
      (∀ b : ℝ, 0 < b →
        ENNReal.ofReal (1 - Real.exp (-(φ / 2) * b)) ≤
          ν (Iic b)) := by
  obtain ⟨ν, hprob, hcdf, hlow⟩ :=
    chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
      X q φ hq hφ hroot
  obtain ⟨μ, hfin, hsupp, hcdfμ⟩ :=
    chat04_esscher_perpetual_infimum_finite_nonnegative_distribution
      X φ (le_of_lt hφ)
  have hEq : ν = μ := by
    apply Measure.ext_of_Iic
    intro x
    exact (hcdf x).trans (hcdfμ x).symm
  have hsupport : ν (Iio (0 : ℝ)) = 0 := by
    rw [hEq]
    exact hsupp
  letI : IsProbabilityMeasure ν := hprob
  refine ⟨ν, hprob, hsupport, hcdf, ?_, hlow⟩
  intro β hβ
  exact positiveLaplace_cumulative_measure ν β hβ hsupport
