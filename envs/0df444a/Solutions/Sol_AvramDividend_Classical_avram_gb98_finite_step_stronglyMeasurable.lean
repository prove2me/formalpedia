-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb98_finite_step_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:19:27.011421+00:00
-- url     : https://prove2.me/submissions/d61b9512-e513-4c14-b062-bd6ad67d32bd

import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (s : Finset ℕ) (a b : ℕ → ℝ) (g : ℕ → Ω → ℝ)
    (hg : ∀ i ∈ s, StronglyMeasurable (g i)) (t : ℝ) :
    StronglyMeasurable (fun ω =>
      s.sum (fun i => if a i ≤ t ∧ t < b i then g i ω else 0)) := by
  classical
  have hf : ∀ i ∈ s, StronglyMeasurable
      (fun ω => if a i ≤ t ∧ t < b i then g i ω else 0) := by
    intro i hi
    by_cases h : a i ≤ t ∧ t < b i
    · simpa [h] using hg i hi
    · simpa [h] using
        (stronglyMeasurable_const : StronglyMeasurable (fun _ : Ω => (0 : ℝ)))
  have hsum := Finset.stronglyMeasurable_sum s hf
  have heq :
      (∑ i ∈ s, (fun ω : Ω =>
        if a i ≤ t ∧ t < b i then g i ω else 0)) =
      (fun ω => ∑ i ∈ s,
        if a i ≤ t ∧ t < b i then g i ω else 0) := by
    funext ω
    simp
  rw [← heq]
  exact hsum
