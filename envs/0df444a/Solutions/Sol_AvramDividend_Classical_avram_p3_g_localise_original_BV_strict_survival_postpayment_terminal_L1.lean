-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:02:45.306566+00:00
-- url     : https://prove2.me/submissions/6a37dc1d-c63a-4c8b-9ed1-cbc549e7a21e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original BV right-horizon postpayment terminal is integrable
for every deterministic time and finite or infinite cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0) (hfinite : IsFiniteMeasure P)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (S : ℝ≥0) :
    Integrable (fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) P := by
  have hPre :
      Integrable (fun ω : Ω =>
        if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (S : ℝ))) *
            w (riskProcess X x D S ω)
        else 0) P :=
    avram_p3_bv_original_strict_preterminal_L1
      X hBV hXzero hfinite x D hD.1.1
      w hw_cont hw_neg q S
  have hAd :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD.1.1 w hw_cont hw_neg).2
  have hWmeas :
      Measurable (fun ω : Ω =>
        w (x + X.X S ω - rightLimit D S ω)) :=
    hAd.measurable
  have hEvent :
      MeasurableSet {ω : Ω | (S : ℝ≥0∞) < ruinTime X x D ω} :=
    measurableSet_Ioi.preimage
      (ruinTime_measurable X x D hD.1.1)
  have hTermMeas :
      Measurable (fun ω : Ω =>
        if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (S : ℝ))) *
            w (x + X.X S ω - rightLimit D S ω)
        else 0) :=
    Measurable.ite hEvent (measurable_const.mul hWmeas) measurable_const
  apply Integrable.mono hPre hTermMeas.aestronglyMeasurable
  filter_upwards [] with ω
  obtain ⟨hNonneg, hBound⟩ :=
    avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
      X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hx hxc D hD q hjump ω S
  have hPreNonneg :
      0 ≤ (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (riskProcess X x D S ω)
      else 0) :=
    le_trans hNonneg hBound
  simp only [Real.norm_eq_abs, abs_of_nonneg hNonneg,
    abs_of_nonneg hPreNonneg]
  exact hBound
