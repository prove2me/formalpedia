-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_hjump_positive_stopped_rightpayment_tsum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:05:09.817597+00:00
-- url     : https://prove2.me/submissions/bfccaa46-048e-4d87-bb5c-61c88098ed3a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_hjump_discounted_postsource_rightpayment_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- The source P4-F right-jump secant signs the whole summable positive
payment set, with the original post-X, pre-right-D reserve ordering. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (B : Set ℝ≥0)
    (hB : ∀ t : B,
      (t : ℝ≥0) = 0 ∨ ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hSummable : Summable (fun t : B =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∑' t : B, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by
  apply tsum_nonpos
  intro t
  exact avram_p4_d_dividend_original_hjump_discounted_postsource_rightpayment_nonpos
    X x D w hjump ω (t : ℝ≥0) (hB t) q
