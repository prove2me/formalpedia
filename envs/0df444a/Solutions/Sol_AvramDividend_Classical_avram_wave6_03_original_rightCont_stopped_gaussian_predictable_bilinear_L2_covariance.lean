-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_L2_covariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:21:45.849915+00:00
-- url     : https://prove2.me/submissions/68b4af46-7943-4e81-895c-dc417798be0a

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_quadratic_energy_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- The authentic same-path stopped Gaussian bilinear L² covariance. -/
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
    (hHbound : ∀ ω, |H ω| ≤ BH) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    MemLp (fun ω => G ω * Y ω) 2 P ∧
    MemLp (fun ω => H ω * Y ω) 2 P ∧
      (∫ ω, (G ω * Y ω) * (H ω * Y ω) ∂P) =
        (∫ ω, G ω * H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  dsimp only
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hstop :
      IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hGL2 : MemLp (fun ω => G ω * Y ω) 2 P :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν τ hstop T hbounded h G
        hGglobal.stronglyMeasurable BG hBG hGbound
  have hHL2 : MemLp (fun ω => H ω * Y ω) 2 P :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν τ hstop T hbounded h H
        hHglobal.stronglyMeasurable BH hBH hHbound
  have hQuadratic :
      (∫ ω, (G ω * H ω) * Y ω ^ 2 ∂P) =
      (∫ ω, G ω * H ω ∂P) * ((h : ℝ) * X.σ ^ 2) :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_quadratic_energy_exact
      X hν τ hτ T hbounded h (fun ω => G ω * H ω)
        (hGstop.mul hHstop) (hGglobal.mul hHglobal)
  have hfun :
      (fun ω => (G ω * Y ω) * (H ω * Y ω)) =
      (fun ω => (G ω * H ω) * Y ω ^ 2) := by
    funext ω
    ring
  constructor
  · exact hGL2
  constructor
  · exact hHL2
  · rw [hfun]
    exact hQuadratic
