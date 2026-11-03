-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_finite_stieltjes_integrable_from_C1_direct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:46:21.633272+00:00
-- url     : https://prove2.me/submissions/7fc89adb-1ca8-43ba-95c3-8a18d0e6e58a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_actual_discounted_dividend_gradient_integrable_on_finite_payment_window
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original-source BV C1 compactness with an absolute derivative image bound and finite Stieltjes mass make the actual localized discounted dividend-gradient correction integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (A : Set ℝ) (hAm : MeasurableSet A)
    (hAwindow : A ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
    (hApos : ∀ t ∈ A, 0 ≤ t)
    (hReserveBand : ∀ t ∈ A,
      riskProcess X x D t.toNNReal ω ∈ Icc a b)
    (hMeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      ((dividendMeasure D ω).restrict A)) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω) := by
  have hOpen : IsOpen
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen C
  have hCont :
      ContinuousOn (deriv w)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hwC1.continuousOn_deriv_of_isOpen hOpen (by norm_num)
  have hContBand : ContinuousOn (deriv w) (Icc a b) :=
    hCont.mono hBand
  obtain ⟨K, hK⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hContBand
  have hKnonneg : 0 ≤ |K| := abs_nonneg K
  have hDerivPath : ∀ t ∈ A,
      |deriv w (riskProcess X x D t.toNNReal ω)| ≤ |K| := by
    intro t ht
    have hb : ‖deriv w (riskProcess X x D t.toNNReal ω)‖ ≤ K :=
      hK _ (hReserveBand t ht)
    have hb' : |deriv w (riskProcess X x D t.toNNReal ω)| ≤ K := by
      simpa only [Real.norm_eq_abs] using hb
    exact hb'.trans (le_abs_self K)
  exact
    avram_wave7_02_original_BV_actual_discounted_dividend_gradient_integrable_on_finite_payment_window
      X x D hD ω T q hq w A hAm hAwindow hApos
      |K| hKnonneg hDerivPath hMeas
