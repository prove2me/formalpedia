-- Prove2me | solution 2 for AvramDividend.Classical.chat04_esscher_compensated_leftshift_reward_strongly_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:06:54.618739+00:00
-- url     : https://prove2.me/submissions/c7e68f14-3f5a-4537-a9fe-c35b335baed2

import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

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
  have hmX : Measurable[𝓕 t] (X.X t) := X.adapted t
  have hmZ : Measurable[𝓕 t]
      (fun ω : Ω => Real.exp
        (-ε * X.X t ω -
          (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ))) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul hmX).sub measurable_const)
  exact hmZ.stronglyMeasurable
