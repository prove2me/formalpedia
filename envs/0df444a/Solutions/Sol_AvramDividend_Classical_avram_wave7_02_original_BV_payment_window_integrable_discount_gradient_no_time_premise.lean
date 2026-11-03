-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_payment_window_integrable_discount_gradient_no_time_premise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:48:08.976684+00:00
-- url     : https://prove2.me/submissions/74029c67-8288-4520-80ea-815e5d842167

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_actual_discounted_dividend_gradient_integrable_on_finite_payment_window
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Genuine finite payment-window support supplies nonnegative clock automatically, so the discounted physical derivative is integrable without an independent time-sign premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (A : Set ℝ) (hAm : MeasurableSet A)
    (hAwindow : A ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
    (K : ℝ) (hK : 0 ≤ K)
    (hDerivativeBound : ∀ t ∈ A,
      |deriv w (riskProcess X x D t.toNNReal ω)| ≤ K)
    (hMeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      ((dividendMeasure D ω).restrict A)) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω) := by
  refine
    avram_wave7_02_original_BV_actual_discounted_dividend_gradient_integrable_on_finite_payment_window
      X x D hD ω T q hq w A hAm hAwindow ?_
      K hK hDerivativeBound hMeas
  intro t ht
  exact
    (paymentTimes_membership_to_nNReal_active
      (ruinTime X x D ω) t (hAwindow ht).1).1
