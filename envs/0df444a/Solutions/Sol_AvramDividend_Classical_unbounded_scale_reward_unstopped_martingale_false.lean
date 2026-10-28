-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_reward_unstopped_martingale_false
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:35:15.980751+00:00
-- url     : https://prove2.me/submissions/8de54663-cf32-4611-b45b-2e75906d1d6d

import Theorems.Thm_AvramDividend_Classical_unbounded_discounted_scale_unstopped_martingale_impossible
import Mathlib.Probability.Process.Filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal

/-- The original un-killed scale martingale claim is inconsistent with the
spectrally negative Lévy model under unbounded variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ¬ Martingale
      (fun t : ℝ≥0 => fun ω : Ω =>
        Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) 𝓕 P := by
  letI : IsProbabilityMeasure P := X.isProbability
  letI : SigmaFiniteFiltration P 𝓕 := inferInstance
  exact unbounded_discounted_scale_unstopped_martingale_impossible
    X q hq W hW hnbv
