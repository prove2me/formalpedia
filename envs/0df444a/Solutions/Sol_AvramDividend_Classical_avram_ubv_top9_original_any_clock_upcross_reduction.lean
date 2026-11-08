-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_any_clock_upcross_reduction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:53:05.524205+00:00
-- url     : https://prove2.me/submissions/c4bd0da9-a413-4a40-aac2-99e044e90a5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_upcross_localisation
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_compact_original_reward_L1_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_upcross_fatou_budget_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Construct bounded upcross clocks and pass true source rewards through Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCtop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ T)
    (hCashρI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hLocalBudget : ∀ (κ : ℕ → Ω → ℝ≥0)
      (hκstop : ∀ j, IsStoppingTime 𝓕.rightCont
        (fun ω => (κ j ω : WithTop ℝ≥0)))
      (hκle : ∀ j ω, κ j ω ≤ ρ ω)
      (hκbound : ∀ j ω, X.X (κ j ω) ω ≤ (j : ℝ) + 1)
      (H : ℕ → Ω → ℝ),
      (∀ j ω, H j ω =
        Real.exp (-(q * (κ j ω : ℝ))) *
          w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
            else riskProcess X x D (κ j ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) →
      ∀ j, (∫ ω, H j ω ∂P) ≤ w x) :
    (∫ ω, F ω ∂P) ≤ w x := by
  classical
  obtain ⟨κ, hκstop, hκle, hκbound, hEventually⟩ :=
    avram_ubv_top9_original_any_clock_upcross_localisation
      X T ρ hρstop hρle
  let H : ℕ → Ω → ℝ := fun j ω =>
    Real.exp (-(q * (κ j ω : ℝ))) *
      w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
      else riskProcess X x D (κ j ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  have hHsource : ∀ j ω, H j ω =
      Real.exp (-(q * (κ j ω : ℝ))) *
        w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
        else riskProcess X x D (κ j ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal :=
    fun _ _ => rfl
  have hHI : ∀ j, Integrable (H j) P := fun j =>
    (avram_ubv_top9_compact_original_reward_L1_nonnegative
      X hBV q (le_of_lt hq) w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD ρ hCashρI κ hκstop hκle hκbound H hHsource j).1
  exact avram_ubv_top9_original_upcross_fatou_budget_transfer
    X hBV w C hC hCtop hw0 hw_cont hw_neg hw_smooth hw_grad
    x hxc D hD q ρ hρstop F hFsource κ hκstop H hHsource
    hHI hEventually (hLocalBudget κ hκstop hκle hκbound H hHsource)
