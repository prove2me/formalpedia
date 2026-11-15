-- Prove2me | solution 1 for AvramDividend.Classical.avram_b245_original_ruinclipped_allclock_inclusive_cash_terminal_to_strict_reduction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:31:25.62393+00:00
-- url     : https://prove2.me/submissions/bba32d3b-1a15-4903-a3f6-75188b3b15bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b244_original_ruinclipped_positive_stop_inclusive_Iic_cash_terminal_contact_le_strict
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ η (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D t η - D t η ≤
        w (riskProcess X x D t η) -
          w (riskProcess X x D t η -
            (rightLimit D t η - D t η)))
    (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
            (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hZero : ∀ ω, σ ω = 0 → F ω ≤ w x) :
    ∀ ω, F ω ≤
      if σ ω = 0 then w x
      else Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
  intro ω
  by_cases hzero : σ ω = 0
  · simpa only [if_pos hzero] using hZero ω hzero
  · have hpos : 0 < σ ω :=
      lt_of_le_of_ne (by positivity) (Ne.symm hzero)
    simpa only [if_neg hzero] using
      (avram_b244_original_ruinclipped_positive_stop_inclusive_Iic_cash_terminal_contact_le_strict
        X x C D hD w q hq hjump σ F hFsource ω hpos)
