-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb102_finite_step_joint_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:27:14.898767+00:00
-- url     : https://prove2.me/submissions/d1d09163-7cd0-4eb3-b874-e00f21f0ee10

import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (s : Finset ℕ) (a b : ℕ → ℝ) (g : ℕ → Ω → ℝ)
    (hg : ∀ i ∈ s, StronglyMeasurable (g i)) :
    StronglyMeasurable (fun z : ℝ × Ω =>
      s.sum (fun i =>
        if a i ≤ z.1 ∧ z.1 < b i then g i z.2 else 0)) := by
  classical
  have hf : ∀ i ∈ s, StronglyMeasurable
      (fun z : ℝ × Ω =>
        if a i ≤ z.1 ∧ z.1 < b i then g i z.2 else 0) := by
    intro i hi
    have hc : MeasurableSet
        {z : ℝ × Ω | a i ≤ z.1 ∧ z.1 < b i} := by
      measurability
    have hgi : StronglyMeasurable (fun z : ℝ × Ω => g i z.2) :=
      (hg i hi).comp_measurable measurable_snd
    exact StronglyMeasurable.ite hc hgi stronglyMeasurable_const
  have hsum := Finset.stronglyMeasurable_sum s hf
  have heq :
      (∑ i ∈ s, (fun z : ℝ × Ω =>
        if a i ≤ z.1 ∧ z.1 < b i then g i z.2 else 0)) =
      (fun z => ∑ i ∈ s,
        if a i ≤ z.1 ∧ z.1 < b i then g i z.2 else 0) := by
    funext z
    simp
  rw [← heq]
  exact hsum
