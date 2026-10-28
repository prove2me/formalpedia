-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_finite_horizon_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:37:34.571922+00:00
-- url     : https://prove2.me/submissions/c877c325-5343-4e2a-b8a1-4b2b06ec7b1e

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    IsProbabilityMeasure
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let m : Ω → ℝ := fun ω => Real.exp (θ * X.X t ω -
    (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)
  have hInt : Integrable m P := by
    simpa only [m] using esscher_exp_process_integrable X θ hθ t
  have hUnit : (∫ ω, m ω ∂P) = 1 := by
    simpa only [m, SpectrallyNegativeLevy.ψ] using
      levy_compensated_exponential_expectation_one X t θ hθ
  have hNonneg : ∀ ω : Ω, 0 ≤ m ω := fun ω => Real.exp_nonneg _
  have hLin : (∫⁻ ω, ENNReal.ofReal (m ω) ∂P) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall hNonneg)]
    rw [hUnit]
    simp
  constructor
  change P.withDensity (fun ω => ENNReal.ofReal (m ω)) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ]
  simpa only [Measure.restrict_univ] using hLin
