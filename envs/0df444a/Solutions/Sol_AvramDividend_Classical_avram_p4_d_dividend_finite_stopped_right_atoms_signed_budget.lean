-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_finite_stopped_right_atoms_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:31:31.678022+00:00
-- url     : https://prove2.me/submissions/c41a0ef7-e863-4681-bd37-6ac3abefdc52

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- The exact finite stopped right-dividend jump corrections of the original source have nonpositive discounted sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (ω : Ω) (T : ℝ≥0) (s : Finset ℝ≥0)
    (hstop : ∀ t ∈ s, (t : ℝ) ≤ (T : ℝ))
    (hactive : ∀ t ∈ s,
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ s, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro t ht
  have hsec := hjump ω t (hactive t ht)
  have hunit :
      (rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω) ≤ 0 := by
    linarith only [hsec]
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) hunit