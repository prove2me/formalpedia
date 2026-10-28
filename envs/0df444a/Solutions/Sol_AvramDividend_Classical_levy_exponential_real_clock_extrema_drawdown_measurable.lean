-- Prove2me | solution 1 for AvramDividend.Classical.levy_exponential_real_clock_extrema_drawdown_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:41:51.967777+00:00
-- url     : https://prove2.me/submissions/ee31477f-8fc5-4d24-80f3-96650dddb44e

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-- Supremum, negative infimum and drawdown are jointly measurable at a real clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : Ω × ℝ =>
      ((runningSup X z.2.toNNReal z.1,
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1}),
        runningSup X z.2.toNNReal z.1 -
          X.X z.2.toNNReal z.1)) := by
  have hclock : Measurable
      (fun z : Ω × ℝ => (z.2.toNNReal, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hsup : Measurable
      (fun z : Ω × ℝ => runningSup X z.2.toNNReal z.1) :=
    (levy_runningSup_joint_time_path_measurable X).comp hclock
  have hinf : Measurable
      (fun z : Ω × ℝ =>
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1}) :=
    (levy_running_infimum_joint_time_path_measurable X).comp hclock
  have hstate : Measurable
      (fun z : Ω × ℝ => X.X z.2.toNNReal z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp hclock
  exact (hsup.prodMk hinf).prodMk (hsup.sub hstate)
