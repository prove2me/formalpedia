-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_cash_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:39:44.511754+00:00
-- url     : https://prove2.me/submissions/46b17348-4321-4f55-82da-efbb1a532250

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
/-- The source exponential finite-grid cash including all right-limit
Stieltjes dividend increments is measurable on the original probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (fun ω => θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) P := by
  let Z : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)
  let B : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(θ * rightLimit D t ω))
  have hProd (r v : ℝ≥0) :
      Integrable (fun ω => B r ω * Z v ω) P := by
    change Integrable (fun ω =>
      Real.exp (-(θ * rightLimit D r ω)) *
      Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ)) P
    exact avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
      X D hD θ hθ r v
  have hRightSM (t : ℝ≥0) :
      AEStronglyMeasurable (rightLimit D t) P :=
    ((dividendStrategy_rightLimit_adapted_rightCont D hD t).mono
      (𝓕.rightCont.le t) le_rfl).aestronglyMeasurable
  have hTermSM (i : ℕ) :
      AEStronglyMeasurable (fun ω =>
        θ * (Z (u (i + 1)) ω * B (u (i + 1)) ω *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))) P := by
    have hp := (hProd (u (i + 1)) (u (i + 1))).aestronglyMeasurable
    have hd := (hRightSM (u (i + 1))).sub (hRightSM (u i))
    have hc : AEStronglyMeasurable (fun _ : Ω => θ) P :=
      aestronglyMeasurable_const
    have h := (hc.mul hp).mul hd
    have heq : (fun ω =>
        θ * (Z (u (i + 1)) ω * B (u (i + 1)) ω *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))) =
        (fun ω =>
          (θ * (B (u (i + 1)) ω * Z (u (i + 1)) ω)) *
            (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) := by
      funext ω
      ring
    rw [heq]
    exact h
  have hSumSM (k : ℕ) :
      AEStronglyMeasurable (fun ω =>
        ∑ i ∈ Finset.range k, θ *
          (Z (u (i + 1)) ω * B (u (i + 1)) ω *
            (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))) P := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro i hi
    exact hTermSM i
  change AEStronglyMeasurable (fun ω => θ * ∑ i ∈ Finset.range n,
    Z (u (i + 1)) ω * B (u (i + 1)) ω *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) P
  simpa only [Finset.mul_sum] using hSumSM n
