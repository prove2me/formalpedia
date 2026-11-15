-- Prove2me | solution 1 for AvramDividend.Classical.avram_b189_original_true_random_grid_marked_count_measurable_from_jump_events
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:43:30.339953+00:00
-- url     : https://prove2.me/submissions/ed4fcac1-e309-4c7c-bdcd-c4e0b5a616ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b188_original_random_physical_interval_actual_jump_event_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual original jump-containing cell count of any finite physical stopped grid with ordered measurable random endpoints is a measurable real random variable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i, Measurable (s i)) (ht : ∀ i, Measurable (t i))
    (hst : ∀ ω i, s i ω ≤ t i ω) :
    let J : Ω → Finset ℕ := fun ω =>
      S.filter (fun i => ∃ u : ℝ≥0,
        s i ω < u ∧ u ≤ t i ω ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by
  intro J
  classical
  let A : ℕ → Ω → Prop := fun i ω => ∃ u : ℝ≥0,
    s i ω < u ∧ u ≤ t i ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0
  have hA (i : ℕ) : MeasurableSet {ω : Ω | A i ω} :=
    avram_b188_original_random_physical_interval_actual_jump_event_measurable
      X (s i) (t i) (hs i) (ht i) (fun ω => hst ω i)
  have hSum : Measurable (fun ω =>
      ∑ i ∈ S, if A i ω then (1 : ℝ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hA i) measurable_const measurable_const
  have hEq (ω : Ω) :
      (∑ i ∈ S, if A i ω then (1 : ℝ) else 0) =
        ((J ω).card : ℝ) := by
    simp [J, A, Finset.sum_ite, Finset.sum_const]
  convert hSum using 1
  funext ω
  exact (hEq ω).symm
