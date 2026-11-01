-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_postPayment_exponential_exact_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:28:40.588705+00:00
-- url     : https://prove2.me/submissions/3948f4ba-554b-4eef-8837-e971378440d1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_martingale_finiteGrid_consumption_exact_expectation_balance

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫ ω, ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      (Real.exp (-(θ * rightLimit D (u i) ω)) -
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) ∂P) =
    (∫ ω, Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) -
    (∫ ω, Real.exp (-(θ * rightLimit D (u n) ω)) *
      Real.exp (θ * X.X (u n) ω - (u n : ℝ) * X.ψ θ) ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Y, hYX, hc, hσ, hν⟩ := levy_rightCont_process X
  let Z : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)
  let b : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(θ * rightLimit D t ω))
  have hZ : Martingale Z 𝓕.rightCont P := by
    have hY := levy_compensated_exponential_martingale Y θ hθ
    simpa [Z, SpectrallyNegativeLevy.ψ, hYX, hc, hσ, hν] using hY
  have hBadapt : Adapted 𝓕.rightCont b := by
    intro t
    exact ((measurable_const.mul
      (dividendStrategy_rightLimit_adapted_rightCont D hD t)).neg).exp
  have hBbound : ∀ t ω, 0 ≤ b t ω ∧ b t ω ≤ 1 := by
    intro t ω
    constructor
    · exact (Real.exp_pos _).le
    · have hDnonneg : 0 ≤ D t ω := by
        have hm := (hD.2.1 ω) (zero_le : (0 : ℝ≥0) ≤ t)
        change D 0 ω ≤ D t ω at hm
        rw [hD.1 ω] at hm
        exact hm
      have hright : 0 ≤ rightLimit D t ω :=
        le_trans hDnonneg (dividendStrategy_le_rightLimit D hD ω t)
      have hle : -(θ * rightLimit D t ω) ≤ 0 :=
        neg_nonpos.mpr (mul_nonneg hθ hright)
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
  exact avram_wave4_03_martingale_finiteGrid_consumption_exact_expectation_balance
    Z hZ b hBadapt hBbound u hu n
