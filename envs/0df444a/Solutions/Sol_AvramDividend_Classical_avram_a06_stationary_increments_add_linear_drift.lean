-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_stationary_increments_add_linear_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:50:50.584269+00:00
-- url     : https://prove2.me/submissions/84c96808-6b0e-475b-bf17-a071ede2a290

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LeanLevy_Processes_StochasticProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) (b : ℝ)
    (hZ : HasStationaryIncrements Z P) :
    HasStationaryIncrements (fun t ω => Z t ω + b * (t : ℝ)) P := by
  intro s k
  have h := (hZ s k).add_const (b * (k : ℝ))
  convert h using 1
  · funext ω
    simp only [ProbabilityTheory.increment, Pi.sub_apply, Pi.add_apply]
    push_cast
    ring
  · funext ω
    simp only [ProbabilityTheory.increment, Pi.sub_apply, Pi.add_apply]
    push_cast
    ring
