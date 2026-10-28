-- Prove2me | solution 1 for AvramDividend.Classical.indepSigma_pastWeight_futureReward_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:23:28.079778+00:00
-- url     : https://prove2.me/submissions/a7a91949-b2be-4636-bc2b-ec9d365786cd

import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- A reward of an independent future path factors from every measurable past weight. -/
theorem solution
    {Ω β : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace β] {mPast : MeasurableSpace Ω}
    (P : Measure Ω)
    (pastWeight : Ω → ℝ≥0∞)
    (hp : Measurable pastWeight)
    (hpPast : Measurable[mPast] pastWeight)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : Indep mPast (MeasurableSpace.comap Y inferInstance) P)
    (reward : β → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ ω, pastWeight ω * reward (Y ω) ∂P) =
      (∫⁻ ω, pastWeight ω ∂P) *
        (∫⁻ ω, reward (Y ω) ∂P) := by
  have hSmall : MeasurableSpace.comap pastWeight inferInstance ≤ mPast :=
    hpPast.comap_le
  have hPair : IndepFun pastWeight Y P :=
    (IndepFun_iff_Indep pastWeight Y P).2
      (indep_of_indep_of_le_left hInd hSmall)
  have hProduct : IndepFun pastWeight (reward ∘ Y) P :=
    hPair.comp measurable_id hr
  have hFactor :=
    lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      hp (hr.comp hY) hProduct
  simpa only [Pi.mul_apply, Function.comp_apply] using hFactor
