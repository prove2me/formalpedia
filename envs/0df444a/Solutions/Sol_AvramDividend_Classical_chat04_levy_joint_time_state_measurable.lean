-- Prove2me | solution 1 for AvramDividend.Classical.chat04_levy_joint_time_state_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:01:49.579357+00:00
-- url     : https://prove2.me/submissions/59340185-eec6-47b5-b0e8-76860f079fee

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Mathlib.Probability.Martingale.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every genuine Lévy process is jointly Borel measurable in time and path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) := by
  apply rightContinuous_measurable_sections_joint_evaluation X.X
  · intro t
    exact (X.adapted t).mono (𝓕.le _) le_rfl
  · intro ω t
    exact X.rightCont ω t
