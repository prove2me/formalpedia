-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_bracket_auto_L1_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:57:37.017604+00:00
-- url     : https://prove2.me/submissions/af4548cd-60c4-4337-8708-4333fc583d6b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bilinear_compensated_bracket_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGglobal : Measurable G) (hHglobal : Measurable H)
    (BG BH : ℝ) (hBG : 0 ≤ BG) (hBH : 0 ≤ BH)
    (hGbound : ∀ ω, |G ω| ≤ BG)
    (hHbound : ∀ ω, |H ω| ≤ BH)
    (hGHInt : Integrable (fun ω => G ω * H ω) P) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    P[(fun ω => (G ω * Y ω) * (H ω * Y ω) -
      ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  dsimp only
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hAuto :=
    avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
      X hν τ hτ T hbounded h G H hGstop hHstop
        hGglobal hHglobal BG BH hBG hBH hGbound hHbound
  have hCrossI :
      Integrable (fun ω => (G ω * Y ω) * (H ω * Y ω)) P :=
    hAuto.1
  have hCell :
      (fun ω => (G ω * Y ω) * (H ω * Y ω)) =
      (fun ω => (G ω * H ω) * Y ω ^ 2) := by
    funext ω
    ring
  have hProductI : Integrable (fun ω =>
      (G ω * H ω) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P := by
    change Integrable (fun ω => (G ω * H ω) * Y ω ^ 2) P
    rw [← hCell]
    exact hCrossI
  exact
    avram_wave6_03_original_rightCont_stopped_gaussian_bilinear_compensated_bracket_condExp_zero
      X hν τ hτ T hbounded h G H hGstop hHstop hGHInt hProductI
