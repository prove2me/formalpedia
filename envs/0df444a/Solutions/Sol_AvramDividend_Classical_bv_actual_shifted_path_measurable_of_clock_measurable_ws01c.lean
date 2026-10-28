-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_shifted_path_measurable_of_clock_measurable_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:02:50.68834+00:00
-- url     : https://prove2.me/submissions/d6271d49-422e-4627-95a6-6430e049015a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω) := by
  have hJoint : Measurable
      (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hAtClock : Measurable (fun ω : Ω => X.X (τ ω) ω) :=
    hJoint.comp (hτ.prodMk measurable_id)
  apply measurable_pi_iff.mpr
  intro t
  have hAtShift :
      Measurable (fun ω : Ω => X.X (τ ω + t) ω) :=
    hJoint.comp ((hτ.add_const t).prodMk measurable_id)
  exact hAtShift.sub hAtClock
