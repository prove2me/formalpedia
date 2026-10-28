-- Prove2me | solution 1 for AvramDividend.Classical.levy_runningSup_joint_time_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:29:07.260606+00:00
-- url     : https://prove2.me/submissions/2b320619-ab49-4b62-a791-675b9ecb3b41

import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_actual
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

/-- The actual running supremum is jointly measurable in horizon and path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : ℝ≥0 × Ω => runningSup X z.1 z.2) := by
  apply rightContinuous_measurable_sections_joint_evaluation (runningSup X)
  · intro t
    exact ((runningSup_isDividendStrategy X).2.2.2 t).mono
      (𝓕.le t) le_rfl
  · intro ω t
    exact runningSup_right_continuous_actual X ω t
