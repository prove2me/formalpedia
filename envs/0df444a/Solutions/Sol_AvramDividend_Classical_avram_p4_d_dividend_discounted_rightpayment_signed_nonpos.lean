-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_discounted_rightpayment_signed_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:31:40.609792+00:00
-- url     : https://prove2.me/submissions/7112268f-e194-4ac2-80d6-767f65d8d17e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postsource_rightpayment_reserve_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- The source-exact right-payment signed budget at each active clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0)
    (hactive : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ) :
    Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω)) ≤ 0 := by
  have hstate := avram_p4_d_dividend_postsource_rightpayment_reserve_eq X x D ω t
  rw [hstate]
  have hsec := hjump ω t hactive
  have hsign :
      (rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω) ≤ 0 := by
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hsign