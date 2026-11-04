-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_fixed_time_postpayment_exponential_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:46:40.64925+00:00
-- url     : https://prove2.me/submissions/0e6c7448-fe10-40c6-8be2-542df1a703a0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_postPayment_discounted_exponential_supermartingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original-source postpayment exponential integrability at finite time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (t : ℝ≥0) :
    Integrable (fun ω => Real.exp
      (θ * (x + X.X t ω - rightLimit D t ω) - (t : ℝ) * q)) P := by
  exact (avram_wave4_03_postPayment_discounted_exponential_supermartingale
    X x D hD θ q hθ hψ).integrable t
