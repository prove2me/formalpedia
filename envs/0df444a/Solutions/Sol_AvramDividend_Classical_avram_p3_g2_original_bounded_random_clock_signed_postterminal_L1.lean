-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:06:03.232634+00:00
-- url     : https://prove2.me/submissions/754785ab-436c-4968-a589-55ca9b235291

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_measurable_random_clock_survival_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true signed post-rightpayment payoff is L1 at any bounded measurable
    random clock, including zero, cap contact and strict ruin exclusion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ) (hτBound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
      else 0) P := by
  have hClip :
      Integrable (fun ω =>
        if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ ω : ℝ))) *
            w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
        else 0) P :=
    avram_wave8_20_original_BV_bounded_measurable_random_clock_survival_terminal_integrable
      X hX hBV q hq w hw_cont hw_neg x C D hD H τ hτMeas hτBound
  have hEq :
      (fun ω =>
        if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ ω : ℝ))) *
            w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
        else 0) =
      (fun ω =>
        if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (τ ω : ℝ))) *
            w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
        else 0) := by
    funext ω
    exact avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed
      X q w C hC hw_cont hw0 hw_smooth hw_grad x hxc D hD τ ω
  rw [← hEq]
  exact hClip
