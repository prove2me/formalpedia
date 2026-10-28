-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_compensated_leftshift_reward_strongly_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:05:55.482928+00:00
-- url     : https://prove2.me/submissions/2513adf2-cb86-422e-93c8-62311b2ddef4

import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) :
    ∀ t : ℝ≥0,
      StronglyMeasurable[𝓕 t]
        (fun ω : Ω => Real.exp
          (-ε * X.X t ω -
            (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ))) := by
  intro t
  have hm : Measurable[𝓕 t]
      (fun ω : Ω => Real.exp
        (-ε * X.X t ω -
          (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ))) :=
    ((measurable_const.mul (X.adapted t)).sub measurable_const).exp
  exact hm.stronglyMeasurable
