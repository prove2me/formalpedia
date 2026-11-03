-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:20:12.459769+00:00
-- url     : https://prove2.me/submissions/65a54b9f-7a9d-49d0-bd9e-bd4e54666c91

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_actual_piecewise_discounted_terminal_auto_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_Cash_measurable_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ W Cash Term : Ω → ℝ,
      (∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) ∧
      (∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
      AEStronglyMeasurable Term P ∧ Integrable Cash P := by
  let W : Ω → ℝ := fun ω =>
    if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (τ ω) ω - rightLimit D (τ ω) ω
    else riskProcess X x D (τ ω) ω
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let Term : Ω → ℝ := fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)
  have hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω := by
    intro ω
    rfl
  have hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
    intro ω
    rfl
  have hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω) := by
    intro ω
    rfl
  have hT : AEStronglyMeasurable Term P :=
    avram_wave6_06_original_actual_piecewise_discounted_terminal_auto_measurable
      X x C D hD w hw_cont hw_neg q τ hτstop W Term hW hTerm
  have hτBound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    rw [hτeq ω]
    exact (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
  have hCI : Integrable Cash P :=
    (avram_wave7_08_source_stopped_Cash_measurable_integrable
      X x C D hD q τ n hτmeas hτBound Cash hCash).1
  exact ⟨W, Cash, Term, hW, hCash, hTerm, hT, hCI⟩
