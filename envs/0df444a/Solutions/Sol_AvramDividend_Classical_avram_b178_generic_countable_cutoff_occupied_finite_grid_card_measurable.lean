-- Prove2me | solution 1 for AvramDividend.Classical.avram_b178_generic_countable_cutoff_occupied_finite_grid_card_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:03:22.523019+00:00
-- url     : https://prove2.me/submissions/219319de-fac3-4ee0-8422-b890276fde63

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Finite-grid occupation by any countable family of measurable source cutoff events has a measurable real occupied-cell cardinal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (S : Finset ℕ) (A : ℕ → ℕ → Ω → Prop)
    (hA : ∀ n i, MeasurableSet {ω : Ω | A n i ω}) :
    let J : Ω → Finset ℕ := fun ω =>
      S.filter (fun i => ∃ n : ℕ, A n i ω)
    Measurable (fun ω => ((J ω).card : ℝ)) := by
  intro J
  classical
  have hEvent (i : ℕ) : MeasurableSet {ω : Ω | ∃ n : ℕ, A n i ω} := by
    simpa only [Set.setOf_exists] using
      (MeasurableSet.iUnion (fun n : ℕ => hA n i))
  have hSum : Measurable (fun ω =>
      ∑ i ∈ S, if ∃ n : ℕ, A n i ω then (1 : ℝ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hEvent i) measurable_const measurable_const
  have hCard (ω : Ω) :
      (∑ i ∈ S, if ∃ n : ℕ, A n i ω then (1 : ℝ) else 0) =
        ((J ω).card : ℝ) := by
    simp [J, Finset.sum_ite, Finset.sum_const]
  convert hSum using 1
  funext ω
  exact (hCard ω).symm
