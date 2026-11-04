-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_finite_rightjump_residual_sum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:39:13.727442+00:00
-- url     : https://prove2.me/submissions/8c41fd14-52e9-4d01-ad2a-696b1502c8c1

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

/-- Finite right-payment residuals sum to a nonpositive amount. -/
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
    (ω : Ω) (F : Finset ℝ≥0)
    (hpre : ∀ t ∈ F, t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ F, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro t ht
  simpa using
    (avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
      X x D w q hjump (fun _ => t) ω (hpre t ht))
