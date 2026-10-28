-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteGrid_stoppedEvent_futureReward_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:20:45.289754+00:00
-- url     : https://prove2.me/submissions/4fb6f89c-da70-4f87-b3fd-caeb34bcf6b0

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_grid_state_future_lintegral_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- A finite-grid stopped-history event is an admissible Markov–Tonelli history observable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ι → ℝ≥0) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet[𝓕 (s i)] (A i))
    (hFinite : ∀ i, ∀ I : Finset ℝ≥0,
      Indep (⨆ t ∈ I,
        MeasurableSpace.comap
          (fun ω => X.X (s i + t) ω - X.X (s i) ω) inferInstance)
        (𝓕 (s i)) P)
    (f : ι → ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∑ i, ∫⁻ ω,
      f i (Set.indicator (A i) (fun _ : Ω => (1 : ℝ)) ω,
        (fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω)) ∂P) =
      ∑ i, ∫⁻ h, ∫⁻ y, f i (h, y)
        ∂(Measure.map
          (fun ω => fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω) P)
        ∂(Measure.map
          (Set.indicator (A i) (fun _ : Ω => (1 : ℝ))) P) := by
  classical
  have hH : ∀ i, Measurable[𝓕 (s i)]
      (fun ω : Ω => Set.indicator (A i) (fun _ : Ω => (1 : ℝ)) ω) := by
    intro i
    exact measurable_const.indicator (hA i)
  exact finite_grid_state_future_lintegral_sum X s
    (fun i ω => Set.indicator (A i) (fun _ : Ω => (1 : ℝ)) ω)
    hH hFinite f hf
