-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:46:06.676934+00:00
-- url     : https://prove2.me/submissions/d0d87b54-f93e-41cc-b69a-465069048b57

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
/-- The original source exponential martingale remains integrable after a
bounded, adapted same-path postpayment Stieltjes exponential discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (r v : ℝ≥0) :
    Integrable (fun ω =>
      Real.exp (-(θ * rightLimit D r ω)) *
      Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Y, hYX, hc, hσ, hν⟩ := levy_rightCont_process X
  let Z : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)
  let B : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(θ * rightLimit D t ω))
  have hZ : Martingale Z 𝓕.rightCont P := by
    have hY := levy_compensated_exponential_martingale Y θ hθ
    simpa [Z, SpectrallyNegativeLevy.ψ, hYX, hc, hσ, hν] using hY
  have hBadapt : Adapted 𝓕.rightCont B := by
    intro t
    exact ((measurable_const.mul
      (dividendStrategy_rightLimit_adapted_rightCont D hD t)).neg).exp
  have hBbound : ∀ ω, 0 ≤ B r ω ∧ B r ω ≤ 1 := by
    intro ω
    constructor
    · exact (Real.exp_pos _).le
    · have hDnonneg : 0 ≤ D r ω := by
        have hm := (hD.2.1 ω) (zero_le : (0 : ℝ≥0) ≤ r)
        change D 0 ω ≤ D r ω at hm
        rw [hD.1 ω] at hm
        exact hm
      have hright : 0 ≤ rightLimit D r ω :=
        le_trans hDnonneg (dividendStrategy_le_rightLimit D hD ω r)
      have hle : -(θ * rightLimit D r ω) ≤ 0 :=
        neg_nonpos.mpr (mul_nonneg hθ hright)
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
  have hBsm : AEStronglyMeasurable (B r) P :=
    ((hBadapt r).mono (𝓕.rightCont.le r) le_rfl).aestronglyMeasurable
  have hBnorm : ∀ᵐ ω ∂P, ‖B r ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hBbound ω).1]
    exact (hBbound ω).2
  change Integrable (fun ω => B r ω * Z v ω) P
  exact (hZ.integrable v).bdd_mul hBsm hBnorm