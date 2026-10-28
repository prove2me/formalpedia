-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_randomAge_whole_shiftedPath_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:28:50.40746+00:00
-- url     : https://prove2.me/submissions/9f6f996e-4fbd-48eb-b104-53712b5f49f9

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Whole Levy shifted-path measurability at any measurable finite random age.
The capped upper first-record age requires only its own measurability, not a
stopping-time assertion for an unaugmented filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω) := by
  have hJoint : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hEnd : Measurable (fun ω : Ω => X.X (τ ω) ω) :=
    hJoint.comp (hτ.prodMk measurable_id)
  exact measurable_pi_lambda _ (fun t =>
    (hJoint.comp ((hτ.add measurable_const).prodMk measurable_id)).sub hEnd)
