-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_ae_hjump_positivepart_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:00:02.36835+00:00
-- url     : https://prove2.me/submissions/5bfc8a42-8d50-4010-b73a-b7ce7cac2852

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_hjump_signed_positivepart_stopped_lintegral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal original right-dividend residual has zero positive part at every
    random finite clock, hence almost surely at P4-F's stopped clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (τ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)) *
          ((rightLimit D s.toNNReal ω - D s.toNNReal ω) +
            w (riskProcess X x D s.toNNReal ω -
              (rightLimit D s.toNNReal ω - D s.toNNReal ω)) -
            w (riskProcess X x D s.toNNReal ω)))
          ∂(dividendMeasure D ω)) = 0 := by
  apply Filter.Eventually.of_forall
  intro ω
  exact avram_p4_d_dividend_original_hjump_signed_positivepart_stopped_lintegral_zero
    X x q w D hD hjump ω (τ ω : ℝ) (by positivity)