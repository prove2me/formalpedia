-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_stopped_original_reward_eq_closed_horizon_restriction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:02:09.503602+00:00
-- url     : https://prove2.me/submissions/dedf1aa5-8289-49ec-82b5-aeb46885cb5e

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The original stopped-payment reward truncated at real T agrees exactly
with the canonical closed-horizon Stieltjes measure restricted to paymentTimes.
All time-zero and permitted end-point atoms are retained. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (f : ℝ → ℝ≥0∞) :
    (∫⁻ s in paymentTimes τ ∩ Iic (T : ℝ), f s ∂dividendMeasure D ω) =
    (∫⁻ s in paymentTimes τ, f s ∂
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) := by
  let μ : Measure ℝ := dividendMeasure D ω
  have hPaymentNonneg : paymentTimes τ ⊆ Ici (0 : ℝ) := by
    intro s hs
    change s ∈ Ici (0 : ℝ) ∩
      ({0} ∪ {t : ℝ | ENNReal.ofReal t < τ}) at hs
    exact hs.1
  have hCut :
      paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ) =
        paymentTimes τ ∩ Iic (T : ℝ) := by
    ext s
    constructor
    · intro hs
      exact ⟨hs.1, hs.2.2⟩
    · intro hs
      exact ⟨hs.1, ⟨hPaymentNonneg hs.1, hs.2⟩⟩
  have hMeasure :
      (μ.restrict (Icc (0 : ℝ) (T : ℝ))).restrict (paymentTimes τ) =
        μ.restrict (paymentTimes τ ∩ Iic (T : ℝ)) := by
    rw [Measure.restrict_restrict]
    · rw [hCut]
    · exact paymentTimes_measurable τ
  change (∫⁻ s : ℝ, f s ∂μ.restrict (paymentTimes τ ∩ Iic (T : ℝ))) =
    (∫⁻ s : ℝ, f s ∂(μ.restrict (Icc (0 : ℝ) (T : ℝ))).restrict (paymentTimes τ))
  exact congrArg (fun ν : Measure ℝ => ∫⁻ s : ℝ, f s ∂ν) hMeasure.symm
