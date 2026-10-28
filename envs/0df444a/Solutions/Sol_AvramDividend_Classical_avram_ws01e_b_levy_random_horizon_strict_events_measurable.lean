-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_levy_random_horizon_strict_events_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:38:56.148897+00:00
-- url     : https://prove2.me/submissions/f2ed271f-4ef9-4dda-8902-1809624f30e6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_random_horizon_strict_event_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (e : Θ → ℝ≥0) (he : Measurable e) (a : ℝ) :
    MeasurableSet {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X (e z.2) z.1 - X.X s z.1 < a} ∧
    MeasurableSet {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X s z.1 - X.X 0 z.1 < a} := by
  have hX : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hXT : Measurable (fun z : Ω × Θ => X.X (e z.2) z.1) :=
    hX.comp ((he.comp measurable_snd).prodMk measurable_fst)
  have hL := avram_ws01e_b_joint_random_horizon_strict_event_measurable
    (fun t ω => -X.X t ω) hX.neg
    (fun ω s => (X.rightCont ω s).neg) e he
    (fun z : Ω × Θ => a - X.X (e z.2) z.1)
    (measurable_const.sub hXT)
  have hEqL :
      {z : Ω × Θ | ∃ s : ℝ≥0, s ≤ e z.2 ∧
          X.X (e z.2) z.1 - X.X s z.1 < a} =
      {z : Ω × Θ | ∃ s : ℝ≥0, s ≤ e z.2 ∧
          -X.X s z.1 < a - X.X (e z.2) z.1} := by
    ext z
    constructor
    · rintro ⟨s, hs, h⟩
      exact ⟨s, hs, by linarith⟩
    · rintro ⟨s, hs, h⟩
      exact ⟨s, hs, by linarith⟩
  have hX0 : Measurable (fun z : ℝ≥0 × Ω => X.X 0 z.2) :=
    (X.adapted.measurable).comp measurable_snd
  have hR := avram_ws01e_b_joint_random_horizon_strict_event_measurable
    (fun t ω => X.X t ω - X.X 0 ω) (hX.sub hX0)
    (fun ω s => (X.rightCont ω s).sub continuousWithinAt_const)
    e he (fun _ : Ω × Θ => a) measurable_const
  constructor
  · rw [hEqL]
    exact hL
  · exact hR
