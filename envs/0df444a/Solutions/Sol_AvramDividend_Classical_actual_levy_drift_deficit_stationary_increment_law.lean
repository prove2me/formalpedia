-- Prove2me | solution 1 for AvramDividend.Classical.actual_levy_drift_deficit_stationary_increment_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:29:04.992014+00:00
-- url     : https://prove2.me/submissions/1a236ac6-c8e5-47cb-8f17-fb41cb328ec2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.IdentDistrib
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Compensating the actual Lévy increment by drift preserves stationary
    distribution of the resulting drift-deficit increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    IdentDistrib
      (fun ω => (X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω))
      (fun ω => X.drift * ((t - s : ℝ≥0) : ℝ) -
        X.X (t - s) ω) P P := by
  have hId :
      IdentDistrib
        (fun ω => ((t - s : ℝ≥0) : ℝ) * X.drift -
          (X.X t ω - X.X s ω))
        (fun ω => ((t - s : ℝ≥0) : ℝ) * X.drift -
          X.X (t - s) ω) P P :=
    (X.stationaryIncrements s t hst).const_sub _
  have hFirst :
      (fun ω => (X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω)) =
      (fun ω => ((t - s : ℝ≥0) : ℝ) * X.drift -
        (X.X t ω - X.X s ω)) := by
    funext ω
    rw [NNReal.coe_sub hst]
    ring
  have hSecond :
      (fun ω => X.drift * ((t - s : ℝ≥0) : ℝ) - X.X (t - s) ω) =
      (fun ω => ((t - s : ℝ≥0) : ℝ) * X.drift - X.X (t - s) ω) := by
    funext ω
    ring
  rw [hFirst, hSecond]
  exact hId
