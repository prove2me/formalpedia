-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:52:44.642016+00:00
-- url     : https://prove2.me/submissions/9b1e551c-7f53-4086-ab8d-34ea2d781ef8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original post-X-jump right-dividend correction is nonpositive
at time zero or a strictly pre-ruin stopping time, including horizon atoms. -/
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
    (τ : Ω → ℝ≥0) (ω : Ω)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    Real.exp (-(q * (τ ω : ℝ))) *
      ((rightLimit D (τ ω) ω - D (τ ω) ω) +
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) -
        w (riskProcess X x D (τ ω) ω)) ≤ 0 := by
  have hPost :
      riskProcess X x D (τ ω) ω -
        (rightLimit D (τ ω) ω - D (τ ω) ω) =
      x + X.X (τ ω) ω - rightLimit D (τ ω) ω := by
    simp only [riskProcess]
    ring
  have hSecant := hjump ω (τ ω) hPre
  rw [hPost] at hSecant
  have hSigned :
      (rightLimit D (τ ω) ω - D (τ ω) ω) +
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) -
        w (riskProcess X x D (τ ω) ω) ≤ 0 := by
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) hSigned