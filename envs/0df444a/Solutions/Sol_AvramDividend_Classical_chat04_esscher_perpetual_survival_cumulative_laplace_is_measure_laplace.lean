-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_perpetual_survival_cumulative_laplace_is_measure_laplace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:43:20.125475+00:00
-- url     : https://prove2.me/submissions/120b19a7-659c-44b6-9e1a-63d8739cde51

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_infimum_finite_nonnegative_distribution
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ν (Iio (0 : ℝ)) = 0 ∧
      ∀ β : ℝ, 0 < β →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-β * x)) * (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P))) =
        ENNReal.ofReal (1 / β) *
          (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν) := by
  obtain ⟨ν, hfin, hsupp, hcdf⟩ :=
    AvramDividend.Classical.chat04_esscher_perpetual_infimum_finite_nonnegative_distribution X θ hθ
  refine ⟨ν, hfin, hsupp, fun β hβ => ?_⟩
  simp_rw [← hcdf]
  exact AvramDividend.Classical.positiveLaplace_cumulative_measure ν β hβ hsupp
