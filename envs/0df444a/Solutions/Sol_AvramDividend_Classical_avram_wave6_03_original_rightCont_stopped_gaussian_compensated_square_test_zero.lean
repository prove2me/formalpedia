-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_compensated_square_test_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:12:48.272071+00:00
-- url     : https://prove2.me/submissions/8f76adf4-7f40-4243-817a-244a8f93c2e8

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance

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
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H)
    (hHIntegrable : Integrable H P)
    (hWeightedIntegrable : Integrable (fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => H ω * ((X.X (τ ω + h) ω -
      X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 - (h : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, H ω * ((X.X (τ ω + h) ω - X.X (τ ω) ω -
      (h : ℝ) * X.c) ^ 2 - (h : ℝ) * X.σ ^ 2) ∂P) = 0 := by
  classical
  let Y : Ω → ℝ := fun ω => X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let a : ℝ := (h : ℝ) * X.σ ^ 2
  have hI : Integrable (fun ω => H ω * a) P := hHIntegrable.mul_const a
  have hEq : (fun ω => H ω * ((Y ω) ^ 2 - a)) =
      (fun ω => H ω * (Y ω) ^ 2 - H ω * a) := by
    funext ω
    ring
  change Integrable (fun ω => H ω * ((Y ω) ^ 2 - a)) P ∧
    (∫ ω, H ω * ((Y ω) ^ 2 - a) ∂P) = 0
  rw [hEq]
  constructor
  · exact hWeightedIntegrable.sub hI
  · rw [integral_sub hWeightedIntegrable hI]
    have hSquare := avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance
      X hν τ hτ T hbounded h H hH hHglobal
    change (∫ ω, H ω * (Y ω) ^ 2 ∂P) = (∫ ω, H ω ∂P) * a at hSquare
    rw [hSquare]
    simp only [integral_mul_const]
    ring
