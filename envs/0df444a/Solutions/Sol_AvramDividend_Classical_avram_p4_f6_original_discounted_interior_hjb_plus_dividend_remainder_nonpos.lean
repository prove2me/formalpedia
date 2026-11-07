-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_original_discounted_interior_hjb_plus_dividend_remainder_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:26:06.902285+00:00
-- url     : https://prove2.me/submissions/4070853c-7de0-46c5-a636-5771f7758847

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original interior generator and right-payment residual have nonpositive discounted sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (hy : 0 < x + X.X t ω - rightLimit D t ω)
    (hyC : ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) < C) :
    Real.exp (-(q * (t : ℝ))) *
      ((X.generator w (x + X.X t ω - rightLimit D t ω) -
        q * w (x + X.X t ω - rightLimit D t ω)) +
       ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω))) ≤ 0 := by
  have hGen :
      X.generator w (x + X.X t ω - rightLimit D t ω) -
        q * w (x + X.X t ω - rightLimit D t ω) ≤ 0 :=
    (hw_gen _ hy hyC).2
  have hJump :
      (rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω) ≤ 0 := by
    have h := hjump ω t ht
    linarith
  have hCombined :
      (X.generator w (x + X.X t ω - rightLimit D t ω) -
        q * w (x + X.X t ω - rightLimit D t ω)) +
       ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω)) ≤ 0 := by
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hCombined
