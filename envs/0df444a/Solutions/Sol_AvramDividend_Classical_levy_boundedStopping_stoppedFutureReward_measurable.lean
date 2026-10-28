-- Prove2me | solution 1 for AvramDividend.Classical.levy_boundedStopping_stoppedFutureReward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:07:39.449436+00:00
-- url     : https://prove2.me/submissions/24600240-59f4-4b9b-9814-3e8d269cae7f

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_grid_ennrealFutureReward_limit
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Measurable stopped future rewards follow from finite adapted upper grids and right-continuous Lévy paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hg : Continuous g) (hgm : Measurable g) :
    Measurable (Set.indicator A
      (fun ω : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω))) := by
  rcases levy_boundedStopping_grid_ennrealFutureReward_limit
      X τ hstop T hbound g hg with
    ⟨τn, grid, hgrid, hfib, habove, _htime, hconv⟩
  have hfibAll : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s} := by
    intro n s
    by_cases hs : s ∈ grid n
    · exact hfib n s hs
    · have hempty : {ω : Ω | τn n ω = s} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro heq
        exact hs (heq ▸ hgrid n ω)
      simpa [hempty] using
        (MeasurableSet.empty : MeasurableSet[𝓕 s] (∅ : Set Ω))
  have hmeas : ∀ n : ℕ, Measurable (Set.indicator A
      (fun ω : Ω => g (fun t : ℝ≥0 =>
        X.X (τn n ω + t) ω - X.X (τn n ω) ω))) := by
    intro n
    exact levy_stoppedHistory_gridFutureReward_measurable
      X τ A hA τn habove hfibAll n (grid n) (hgrid n) g hgm
  apply ENNReal.measurable_of_tendsto hmeas
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ A
  · simpa only [Set.indicator_of_mem hω] using hconv ω
  · simp only [Set.indicator_of_notMem hω, tendsto_const_nhds]
