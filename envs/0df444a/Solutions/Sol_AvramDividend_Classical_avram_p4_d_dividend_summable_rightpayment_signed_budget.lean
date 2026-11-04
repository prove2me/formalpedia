-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_summable_rightpayment_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:31:37.101691+00:00
-- url     : https://prove2.me/submissions/1c5b70db-f215-4c5b-ac75-fdb622bedc3f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postsource_rightpayment_reserve_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- The signed right-payment mass is nonpositive after aggregation. -/
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
    (ω : Ω) (A : Set ℝ≥0)
    (hactive : ∀ t : A, (t : ℝ≥0) = 0 ∨
      ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ)
    (hsummable : Summable (fun t : A =>
      Real.exp (-(q * (((t : ℝ≥0) : ℝ)))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∑' t : A,
      Real.exp (-(q * (((t : ℝ≥0) : ℝ)))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) -
          w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by
  apply tsum_nonpos
  intro t
  have hstate :=
    avram_p4_d_dividend_postsource_rightpayment_reserve_eq
      X x D ω (t : ℝ≥0)
  have hsec := hjump ω (t : ℝ≥0) (hactive t)
  have hunit :
      (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (x + X.X (t : ℝ≥0) ω -
          rightLimit D (t : ℝ≥0) ω) -
        w (riskProcess X x D (t : ℝ≥0) ω) ≤ 0 := by
    rw [hstate]
    linarith only [hsec]
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) hunit