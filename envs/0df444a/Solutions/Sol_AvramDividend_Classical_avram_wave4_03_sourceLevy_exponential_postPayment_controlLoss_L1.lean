-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_exponential_postPayment_controlLoss_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:53:12.468781+00:00
-- url     : https://prove2.me/submissions/5717f657-4d75-4d12-a53f-2be3037db785

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
/-- The actual original source Lévy control-loss difference is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (r v : ℝ≥0) :
    Integrable (fun ω =>
      Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ) *
      (Real.exp (-(θ * rightLimit D r ω)) -
        Real.exp (-(θ * rightLimit D v ω)))) P := by
  have h1 :=
    avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
      X D hD θ hθ r v
  have h2 :=
    avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
      X D hD θ hθ v v
  have heq : (fun ω =>
      Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ) *
      (Real.exp (-(θ * rightLimit D r ω)) -
        Real.exp (-(θ * rightLimit D v ω)))) =
      (fun ω =>
        Real.exp (-(θ * rightLimit D r ω)) *
          Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ) -
        Real.exp (-(θ * rightLimit D v ω)) *
          Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ)) := by
    funext ω
    ring
  rw [heq]
  exact h1.sub h2
