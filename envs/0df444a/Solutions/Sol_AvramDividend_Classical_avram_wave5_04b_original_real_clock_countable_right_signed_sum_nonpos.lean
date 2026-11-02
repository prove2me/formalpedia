-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_real_clock_countable_right_signed_sum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:45:29.587275+00:00
-- url     : https://prove2.me/submissions/3892c6f6-fa27-4cee-9000-8fb0a9bcb6e0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The real-clock absolutely summable countable chronological right-payment signed correction is nonpositive at every boundary and at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (ω : Ω) (q : ℝ)
    (hjump : ∀ t : ℝ≥0,
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (A : Set ℝ) (hCount : A.Countable)
    (hNonneg : ∀ t : A, 0 ≤ (t : ℝ))
    (hA : ∀ t : A,
      ((t : ℝ).toNNReal) = 0 ∨
        (((t : ℝ).toNNReal) : ℝ≥0∞) < ruinTime X x D ω)
    (hSummable : Summable (fun t : A => Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((t : ℝ).toNNReal) ω -
          (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((t : ℝ).toNNReal) ω)))) :
    (∑' t : A, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((t : ℝ).toNNReal) ω -
          (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((t : ℝ).toNNReal) ω))) ≤ 0 := by
  apply tsum_nonpos
  intro t
  have hDrop := hjump ((t : ℝ).toNNReal) (hA t)
  have hResidual :
      (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((t : ℝ).toNNReal) ω -
          (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((t : ℝ).toNNReal) ω) ≤ 0 := by
    linarith only [hDrop]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hResidual
