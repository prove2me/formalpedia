-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_zero_of_ae_instant_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:37:30.012253+00:00
-- url     : https://prove2.me/submissions/f904302c-cba9-4529-aba9-3a5d030db939

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_runningSup_reward_zero_at_instant_ruin
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Almost-sure instantaneous ruin forces the stopped reflected reward to vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ)
    (hRuin : ∀ᵐ ω ∂P, barrierRuinTime X a ω = 0) :
    barrierSupValue X a q = 0 := by
  unfold barrierSupValue
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (barrierRuinTime X a ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (runningSup X) ω) ∂P) =
        ∫⁻ _ω : Ω, (0 : ℝ≥0∞) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hRuin] with ω hω
      exact runningSup_reward_zero_at_instant_ruin X a q ω hω
    _ = 0 := by simp
