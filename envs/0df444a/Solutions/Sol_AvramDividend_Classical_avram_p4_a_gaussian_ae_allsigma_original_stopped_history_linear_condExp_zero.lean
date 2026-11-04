-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_allsigma_original_stopped_history_linear_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:40:43.561334+00:00
-- url     : https://prove2.me/submissions/99b2d12a-5f18-491d-95b3-0aa993f9ef7d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual Lévy Gaussian residual has zero stopped-history conditional mean
for any source sigma, including pure-jump sigma zero, given a.s. extraction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ (u : ℝ≥0),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hProdI : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
         Jsmall (τ ω) ω - Jlarge (τ ω) ω))) P) :
    P[(fun ω => H ω *
      (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
         Jsmall (τ ω) ω - Jlarge (τ ω) ω))) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  have hFnAE :
      (fun ω : Ω => H ω *
        (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
          Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
          (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
           Jsmall (τ ω) ω - Jlarge (τ ω) ω))) =ᵐ[P]
      (fun ω : Ω => H ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) := by
    filter_upwards [hSourceDecomp] with ω hω
    rw [hω (τ ω + h), hω (τ ω)]
    push_cast
    ring
  have hProdY : Integrable (fun ω => H ω *
      (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) P :=
    hProdI.congr hFnAE
  have hZero :=
    avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
      Y hYν τ hτ T hbounded h H hH hProdY
  exact (condExp_congr_ae (m := (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace)
    hFnAE).trans hZero