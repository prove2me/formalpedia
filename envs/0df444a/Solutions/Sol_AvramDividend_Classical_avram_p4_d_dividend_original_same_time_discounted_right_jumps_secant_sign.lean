-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_same_time_discounted_right_jumps_secant_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:26:16.9897+00:00
-- url     : https://prove2.me/submissions/4ba1b5de-5616-492d-a3f8-f8da26025845

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- At each exact original post-source/pre-dividend reserve, the explicit
right-payment secant bounds the discounted dividend/value jump remainder. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) +
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) -
          w (riskProcess X x D t ω)) ≤ 0 := by
  intro ω t hpre
  have hSecant := hjump ω t hpre
  have hSigned :
      (rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω) ≤ 0 := by
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hSigned
