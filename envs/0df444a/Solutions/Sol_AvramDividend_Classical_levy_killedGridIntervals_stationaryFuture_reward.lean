-- Prove2me | solution 1 for AvramDividend.Classical.levy_killedGridIntervals_stationaryFuture_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:10:47.489462+00:00
-- url     : https://prove2.me/submissions/dea02e46-8dbe-4205-9d69-820a3a0e1ba2

import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteGrid_stoppedEvent_stationaryFuture_reward
import Theorems.Thm_AvramDividend_Classical_levy_killedExit_gridInterval_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- Killed first-exit grid fibres restart against the common stationary future path law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStationary : ∀ u : ℝ≥0,
      Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (u + t) ω - X.X u ω) P =
      Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
    (r s : ι → ℝ≥0) (hrs : ∀ i, r i ≤ s i)
    (upper lower : ℝ) (A : ι → Set Ω)
    (hA : ∀ i, A i = {ω : Ω |
      (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) < (s i : ℝ≥0∞) ∧
      ¬ (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) < (r i : ℝ≥0∞) ∧
      ¬ ∃ t : ℝ≥0, t < s i ∧ X.X t ω < lower})
    (f : ι → ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∑ i, ∫⁻ ω, f i (Set.indicator (A i) (fun _ : Ω => (1 : ℝ)) ω,
      (fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω)) ∂P) =
    ∑ i, ∫⁻ h, ∫⁻ y, f i (h, y)
      ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
      ∂(Measure.map (Set.indicator (A i) (fun _ : Ω => (1 : ℝ))) P) := by
  have hPast : ∀ i, MeasurableSet[𝓕 (s i)] (A i) := by
    intro i
    rw [hA i]
    exact levy_killedExit_gridInterval_filtration_measurable
      X upper lower (r i) (s i) (hrs i)
  exact levy_finiteGrid_stoppedEvent_stationaryFuture_reward
    X hStationary s A hPast f hf
