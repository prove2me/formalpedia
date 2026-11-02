-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_original_controlled_gradient_stopped_gaussian_L2_isometry_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:26:50.584607+00:00
-- url     : https://prove2.me/submissions/fdaa106e-c3f6-482d-900d-adeb1cf0c2e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_controlled_prejump_gradient_stopped_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact L2 isometry for the genuine capped controlled prepayment Gaussian gradient source cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    let H : Ω → ℝ := stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))
    (∫ ω, (H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) =
      (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  let H : Ω → ℝ := stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))
  have hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hHstopped : Measurable[hstop.measurableSpace] H :=
    avram_wave5_03a_original_controlled_prejump_gradient_stopped_value_measurable
      X x D hD w C hw τ hstop
  have hHg : Measurable H :=
    hHstopped.mono hstop.measurableSpace_le le_rfl
  change (∫ ω, (H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) =
    (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2)
  exact
    avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq
      X hν τ hτ T hbounded h H hHstopped hHg
