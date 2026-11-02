-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_drift_centered_increment_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:59:38.514733+00:00
-- url     : https://prove2.me/submissions/621fa980-4be3-46b4-8500-6ba26c09e448

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (h : ℝ≥0) :
    Measurable (fun ω : Ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) := by
  obtain ⟨Xrc, hpaths, hc, hsig, hmeasure⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hFuture : Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      Xrc.X (τ ω + t) ω - Xrc.X (τ ω) ω) :=
    levy_finiteStopping_stoppedFuturePath_measurable Xrc τ hτ
  rw [hpaths] at hFuture
  exact ((measurable_pi_apply h).comp hFuture).sub measurable_const
