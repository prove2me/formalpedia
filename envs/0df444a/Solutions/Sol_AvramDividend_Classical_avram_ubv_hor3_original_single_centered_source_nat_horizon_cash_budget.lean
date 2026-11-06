-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_single_centered_source_nat_horizon_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:28:10.004204+00:00
-- url     : https://prove2.me/submissions/cf851d16-5afd-4b5a-b406-3e9c13653a6c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_truncated_cash_le_actual_stopped_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (T : ℝ) (τ : Ω → ℝ≥0)
    (hτEq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτStop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term M R : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hMI : Integrable M P) (hMzero : (∫ ω, M ω ∂P) = 0)
    (hRnonpos : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hSource : ∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + R ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hZI : Integrable (fun _ : Ω => (0 : ℝ)) P := by simp
  have hSigned : ∀ᵐ ω ∂P, (0 : ℝ) + 0 ≤ 0 := by simp
  have hUpper : ∀ᵐ ω ∂P, Term ω + Cash ω ≤
      w x + M ω + (0 : ℝ) + 0 := by
    filter_upwards [hSource, hRnonpos] with ω hs hr
    have h : Term ω + Cash ω ≤ w x + M ω := by
      calc
        Term ω + Cash ω ≤ w x + M ω + R ω := hs
        _ ≤ w x + M ω := add_le_of_nonpos_right hr
    simpa using h
  have hNatural :=
    avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
      X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD n hn
      τ hτEq hτMeas hτStop W Cash Term M
      (fun _ : Ω => (0 : ℝ)) (fun _ : Ω => (0 : ℝ))
      hW hCash hTerm hTermMeas hMI hZI hZI hMzero hSigned hUpper
  exact (avram_wave7_08_truncated_cash_le_actual_stopped_clock
    X q x D n hn T).trans hNatural
