-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_F_le_masked_strict_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T22:25:20.786559+00:00
-- url     : https://prove2.me/submissions/db47be5b-4f7a-4a49-8b4a-e6cbbbc34d93

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_positive_clock_paid_post_le_strict_pre

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Source-exact closed-to-strict endpoint ledger; valid at every original stopped physical clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, F ω ≤
      if σ ω = 0 then w x else
        Real.exp (-(q * (σ ω : ℝ))) *
          w (riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
  intro ω
  by_cases hzero : σ ω = 0
  · simp only [if_pos hzero]
    exact avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
      X x q w C D hD hjump σ F hFsource ω hzero
  · have hpos : 0 < σ ω := pos_iff_ne_zero.mpr hzero
    have hbound :=
      avram_ubv_top12_original_positive_clock_paid_post_le_strict_pre
        X x C D hD w q hq hjump ω (σ ω) hpos
    simpa [hFsource ω, hzero] using hbound
