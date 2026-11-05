-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_any_clock_full_cash_post_le_strict_or_zero_initial_from_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:30:28.821094+00:00
-- url     : https://prove2.me/submissions/0d98b6f2-39ed-4eaf-b34f-f1b7fe88c764

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_all_horizon_closed_postreward_le_strict_or_zero_initial
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-exact all-clock inclusive cash plus postpayment is dominated
    by strict cash plus prepayment, except at zero where w(x) pays the
    initial right atom. This applies to sample-dependent clocks pointwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
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
    (τ : Ω → ℝ≥0) :
    ∀ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
      else 0) ≤
      (if τ ω = 0 then w x
      else
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (τ ω : ℝ))) *
            w (riskProcess X x D (τ ω) ω)
        else 0)) := by
  have hJump :
      ∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
          rightLimit D t ω - D t ω ≤
            w (riskProcess X x D t ω) -
              w (riskProcess X x D t ω -
                (rightLimit D t ω - D t ω)) :=
    avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
      X C hC w hw_cont hw_smooth hw_grad x hxc D hD
  intro ω
  exact avram_p3_g2_all_horizon_closed_postreward_le_strict_or_zero_initial
    X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
    x hx hxc D hD hJump ω (τ ω)
