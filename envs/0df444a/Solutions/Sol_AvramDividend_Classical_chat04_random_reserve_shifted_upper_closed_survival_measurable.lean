-- Prove2me | solution 1 for AvramDividend.Classical.chat04_random_reserve_shifted_upper_closed_survival_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:25:32.053996+00:00
-- url     : https://prove2.me/submissions/2978cd57-f32d-4c52-a6d5-3af50e762ad8

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_upper_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Continuous-time upper survival of a shifted random reserve is measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (hH : Measurable H) (a : ℝ) (b T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
        H ω + (X.X (b + v) ω - X.X b ω) ≤ a} := by
  obtain ⟨τ, hCover, hTerminal⟩ :=
    chat04_explicit_shifted_killed_survival_schedule T
  have hXm : ∀ u, Measurable (X.X u) :=
    fun u => (X.adapted u).mono (𝓕.le u) le_rfl
  have hEq :
      {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
        H ω + (X.X (b + v) ω - X.X b ω) ≤ a} =
      ⋂ j : ℕ, {ω : Ω | τ j ≤ T →
        H ω + (X.X (b + τ j) ω - X.X b ω) ≤ a} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact chat04_random_reserve_shifted_upper_closed_survival_schedule_iff
      X H ω a b T τ hCover hTerminal
  rw [hEq]
  refine MeasurableSet.iInter fun j => ?_
  by_cases hj : τ j ≤ T
  · simp only [hj, true_implies]
    exact measurableSet_le
      (hH.add ((hXm (b + τ j)).sub (hXm b))) measurable_const
  · simp [hj]
