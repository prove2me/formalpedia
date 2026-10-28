-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_paymentTimes_iInter_weighted_lintegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:14:47.927029+00:00
-- url     : https://prove2.me/submissions/0bce91a4-09c4-4268-9a7f-7a30f1e3d99d

import Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_restrict_eq
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- All nonnegative Stieltjes reward weights inherit endpoint-nullity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in (⋂ n, paymentTimes (σ n)), f t
      ∂(dividendMeasure (runningSup X) ω)) =
    (∫⁻ t in paymentTimes (⨅ n, σ n), f t
      ∂(dividendMeasure (runningSup X) ω)) := by
  exact congrArg (fun μ : Measure ℝ => ∫⁻ t, f t ∂μ)
    (runningSup_paymentTimes_iInter_restrict_eq X ω σ)
