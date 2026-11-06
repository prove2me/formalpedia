-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_original_bv_ubv_nonnegative_clock_cash_hjb_preflight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:42:16.669878+00:00
-- url     : https://prove2.me/submissions/152f000d-f531-4f2f-8bfe-2d9ef7123d36

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_integer_truncated_ruin_nnreal_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_real_measurable_of_source
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_sweep18_original_uniform_HJB_stopping_criteria

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Source-exact BV/UBV and zero/positive original clock, W/Cash/Term,
    HJB and stopped-payment prerequisites without stochastic assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (n : ℕ) :
    ∃ (τ : Ω → ℝ≥0),
      (∀ ω, τ ω =
        (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      Measurable (fun ω => (τ ω : ℝ)) ∧
      IsStoppingTime 𝓕.rightCont
        (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      ∃ W Cash Term : Ω → ℝ,
        (∀ ω, W ω = if τ ω = 0 ∨
          (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) ∧
        (∀ ω, Cash ω = (∫⁻ s in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) ∧
        (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
        AEStronglyMeasurable Term P ∧ Integrable Cash P ∧
        (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
        (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
        (∀ ω (t : ℝ≥0), 0 < t →
          (t : ℝ≥0∞) < ruinTime X x D ω →
          0 ≤ w (riskProcess X x D t ω)) ∧
        (∀ ω (t : ℝ≥0),
          (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
          rightLimit D t ω - D t ω ≤
            w (riskProcess X x D t ω) -
              w (riskProcess X x D t ω -
                (rightLimit D t ω - D t ω))) := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  have hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    (avram_p3_main_original_integer_truncated_ruin_nnreal_stopping
      X x D hD.1.1 n).2
  have hτmeas : Measurable (fun ω => (τ ω : ℝ)) :=
    avram_wave7_08_actual_truncated_clock_real_measurable_of_source
      X x D n (ruinTime_measurable X x D hD.1.1)
  obtain ⟨W, Cash, Term, hW, hCash, hTerm, hTermMeas, hCashI⟩ :=
    avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
      X x C D hD w hw_cont hw_neg q n τ (by intro ω; rfl)
      hτmeas hτstop
  obtain ⟨hgen, hgrad, hnonneg, hjump⟩ :=
    avram_sweep18_original_uniform_HJB_stopping_criteria
      X q w C hC hw_cont hw0 hw_smooth hw_hjb
      x hx hxc D hD
  exact ⟨τ, (by intro ω; rfl), hτmeas, hτstop,
    W, Cash, Term, hW, hCash, hTerm, hTermMeas, hCashI,
    hgen, hgrad, hnonneg, hjump⟩
