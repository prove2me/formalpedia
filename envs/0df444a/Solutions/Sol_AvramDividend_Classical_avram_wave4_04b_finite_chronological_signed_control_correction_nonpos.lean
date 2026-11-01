-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_finite_chronological_signed_control_correction_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:04:34.261816+00:00
-- url     : https://prove2.me/submissions/13beeb42-f6f0-427f-84d4-5a1485436858

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

set_option maxHeartbeats 1000000 in
/-- Every finite chronological right-dividend correction in the actual
discounted Itô–Meyer jump balance is nonpositive, including the initial
payment atom and any permitted simultaneous source-jump/payment time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ)
    (F : Finset ℝ≥0)
    (hFT : ∀ t ∈ F, t ≤ T)
    (hFP : ∀ t ∈ F, (t : ℝ) ∈ paymentTimes τ)
    (hjump : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    (∑ t ∈ F, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro t ht
  have hJ := hjump t (hFT t ht) (hFP t ht)
  have hCorr :
      (rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω) ≤ 0 := by
    linarith
  have hDiscount : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  exact mul_nonpos_of_nonneg_of_nonpos hDiscount hCorr
