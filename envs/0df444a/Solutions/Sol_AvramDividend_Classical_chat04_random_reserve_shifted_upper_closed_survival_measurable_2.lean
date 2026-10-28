-- Prove2me | solution 2 for AvramDividend.Classical.chat04_random_reserve_shifted_upper_closed_survival_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:26:36.298777+00:00
-- url     : https://prove2.me/submissions/377349ce-25ab-4c7a-93f4-be683fb12b70

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_upper_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (hH : Measurable H) (a : ℝ) (b T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
        H ω + (X.X (b + v) ω - X.X b ω) ≤ a} := by 
  obtain ⟨τ, hC, hT⟩ := chat04_explicit_shifted_killed_survival_schedule T
  have : {ω : Ω | ∀ v : ℝ≥0, v ≤ T → H ω + (X.X (b + v) ω - X.X b ω) ≤ a} =
      ⋂ j : ℕ, {ω | τ j ≤ T → H ω + (X.X (b + τ j) ω - X.X b ω) ≤ a} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact chat04_random_reserve_shifted_upper_closed_survival_schedule_iff X H ω a b T τ hC hT
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  by_cases hj : τ j ≤ T
  · simp only [hj, true_implies]
    exact measurableSet_le (hH.add (((X.adapted (b + τ j)).mono (𝓕.le _) le_rfl).sub
      ((X.adapted b).mono (𝓕.le _) le_rfl))) measurable_const
  · simp [hj]
