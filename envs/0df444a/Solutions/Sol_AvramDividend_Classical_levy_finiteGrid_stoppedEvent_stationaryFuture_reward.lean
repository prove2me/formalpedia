-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteGrid_stoppedEvent_stationaryFuture_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T08:00:10.598309+00:00
-- url     : https://prove2.me/submissions/1efd1411-f7ac-4f56-a305-d5eda7afc429

import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteGrid_stoppedEvent_futureReward_of_increments

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The finite-grid stopped-event reward has the same future-law factor at each grid time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStationary : ∀ u : ℝ≥0,
      Measure.map
        (fun ω : Ω => fun t : ℝ≥0 => X.X (u + t) ω - X.X u ω) P =
      Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
    (s : ι → ℝ≥0) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet[𝓕 (s i)] (A i))
    (f : ι → ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∑ i, ∫⁻ ω,
      f i (Set.indicator (A i) (fun _ : Ω => (1 : ℝ)) ω,
        (fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω)) ∂P) =
      ∑ i, ∫⁻ h, ∫⁻ y, f i (h, y)
        ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
        ∂(Measure.map
          (Set.indicator (A i) (fun _ : Ω => (1 : ℝ))) P) := by
  classical
  calc
    (∑ i, ∫⁻ ω,
      f i (Set.indicator (A i) (fun _ : Ω => (1 : ℝ)) ω,
        (fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω)) ∂P) =
        ∑ i, ∫⁻ h, ∫⁻ y, f i (h, y)
          ∂(Measure.map
            (fun ω => fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω) P)
          ∂(Measure.map
            (Set.indicator (A i) (fun _ : Ω => (1 : ℝ))) P) :=
          levy_finiteGrid_stoppedEvent_futureReward_of_increments X s A hA f hf
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hStationary (s i)]
