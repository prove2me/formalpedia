-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:50:21.539947+00:00
-- url     : https://prove2.me/submissions/d0a4c65c-17f0-42f0-8b85-3a008412125d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_L2_covariance
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_condExp_covariance

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
    (hHbound : ∀ ω, |H ω| ≤ BH) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => (G ω * Y ω) * (H ω * Y ω)) P ∧
    P[(fun ω => (G ω * Y ω) * (H ω * Y ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) := by
  dsimp only
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hL2 :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_L2_covariance
      X hν τ hτ T hbounded h G H hGstop hHstop
        hGglobal hHglobal BG BH hBG hBH hGbound hHbound
  have hGI : MemLp (fun ω => G ω * Y ω) 2 P := hL2.1
  have hHI : MemLp (fun ω => H ω * Y ω) 2 P := hL2.2.1
  have hCrossInt :
      Integrable (fun ω => (G ω * Y ω) * (H ω * Y ω)) P :=
    hGI.integrable_mul hHI
  have hCell :
      (fun ω => (G ω * Y ω) * (H ω * Y ω)) =
      (fun ω => (G ω * H ω) * Y ω ^ 2) := by
    funext ω
    ring
  have hProductInt : Integrable (fun ω =>
      (G ω * H ω) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P := by
    change Integrable (fun ω => (G ω * H ω) * Y ω ^ 2) P
    rw [← hCell]
    exact hCrossInt
  have hCE :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_condExp_covariance
      X hν τ hτ T hbounded h G H hGstop hHstop hProductInt
  exact ⟨hCrossInt, hCE⟩
