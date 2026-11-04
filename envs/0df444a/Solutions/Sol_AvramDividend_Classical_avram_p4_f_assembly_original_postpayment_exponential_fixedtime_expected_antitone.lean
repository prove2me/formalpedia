-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_postpayment_exponential_fixedtime_expected_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:46:38.127784+00:00
-- url     : https://prove2.me/submissions/a5a18d36-87cf-450d-b9c1-bf44ad3c6a36

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_postPayment_discounted_exponential_supermartingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual controlled Lévy discounted exponential expectations decrease in time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, Real.exp
      (θ * (x + X.X t ω - rightLimit D t ω) - (t : ℝ) * q) ∂P) ≤
    (∫ ω, Real.exp
      (θ * (x + X.X s ω - rightLimit D s ω) - (s : ℝ) * q) ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hSM := avram_wave4_03_postPayment_discounted_exponential_supermartingale
    X x D hD θ q hθ hψ
  simpa using (hSM.setIntegral_le hst MeasurableSet.univ)
