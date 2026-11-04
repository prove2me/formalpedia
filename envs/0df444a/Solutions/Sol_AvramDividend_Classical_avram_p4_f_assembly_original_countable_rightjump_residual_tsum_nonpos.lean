-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_countable_rightjump_residual_tsum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:43:06.1346+00:00
-- url     : https://prove2.me/submissions/34439150-f6e7-4c71-8ed0-20f24e946318

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Summable countable right-dividend residuals remain nonpositive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℕ → ℝ≥0)
    (hpre : ∀ k, t k = 0 ∨ (t k : ℝ≥0∞) < ruinTime X x D ω)
    (hsummable : Summable (fun k : ℕ =>
      Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          w (x + X.X (t k) ω - rightLimit D (t k) ω) -
          w (riskProcess X x D (t k) ω)))) :
    (∑' k : ℕ, Real.exp (-(q * (t k : ℝ))) *
      ((rightLimit D (t k) ω - D (t k) ω) +
        w (x + X.X (t k) ω - rightLimit D (t k) ω) -
        w (riskProcess X x D (t k) ω))) ≤ 0 := by
  apply tsum_nonpos
  intro k
  simpa using
    (avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
      X x D w q hjump (fun _ => t k) ω (hpre k))
