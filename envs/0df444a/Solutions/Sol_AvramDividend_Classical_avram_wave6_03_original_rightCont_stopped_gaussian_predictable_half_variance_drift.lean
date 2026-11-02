-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_half_variance_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T00:01:29.144209+00:00
-- url     : https://prove2.me/submissions/ec94f44a-ba4f-4ae3-bdd5-84586a1cb789

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

/-- The genuine source quadratic increment contributes precisely one-half
of its sigma-squared predictable energy to the Ito drift. -/
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
    (hHI : Integrable H P)
    (hWeightedInt : Integrable (fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => (1 / 2 : ℝ) * H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P ∧
    (∫ ω, (1 / 2 : ℝ) * H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      ((h : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H ω ∂P) := by
  classical
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hE :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance
      X hν τ hτ T hbounded h H hH hHglobal
  change (∫ ω, H ω * Y ω ^ 2 ∂P) =
      (∫ ω, H ω ∂P) * ((h : ℝ) * X.σ ^ 2) at hE
  have hFun : (fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) =
      (fun ω => (1 / 2 : ℝ) * (H ω * Y ω ^ 2)) := by
    funext ω
    ring
  change Integrable (fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) P ∧
    (∫ ω, (1 / 2 : ℝ) * H ω * Y ω ^ 2 ∂P) =
      ((h : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H ω ∂P)
  rw [hFun]
  constructor
  · exact hWeightedInt.const_mul (1 / 2 : ℝ)
  · rw [integral_const_mul, hE]
    ring
