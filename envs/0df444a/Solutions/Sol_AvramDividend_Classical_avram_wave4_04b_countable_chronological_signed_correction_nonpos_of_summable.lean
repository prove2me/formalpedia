-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_countable_chronological_signed_correction_nonpos_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:34:15.246538+00:00
-- url     : https://prove2.me/submissions/dd6b9f55-b456-4486-9473-2367fa62fde6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- If its signed countable sum is summable, the full chronological
right-dividend jump correction is nonpositive on the actual stopped
controlled Lévy path, including t=0 and simultaneous source jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ)
    (A : Set ℝ≥0) (hA : A.Countable)
    (hAT : ∀ t : A, (t : ℝ≥0) ≤ T)
    (hAP : ∀ t : A, ((t : ℝ≥0) : ℝ) ∈ paymentTimes τ)
    (hjump : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hSummable : Summable (fun t : A =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∑' t : A,
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by
  apply tsum_nonpos
  intro t
  have hJ := hjump (t : ℝ≥0) (hAT t) (hAP t)
  have hC :
      (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω) ≤ 0 := by
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) hC
