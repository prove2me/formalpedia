-- Prove2me | solution 1 for AvramDividend.Classical.avram_gtop21_nnreal_min_max_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T02:10:14.769381+00:00
-- url     : https://prove2.me/submissions/b3050e36-19e1-4a76-af4a-07dbd0336fce

import Mathlib.Probability.Process.Stopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (a b : Ω → ℝ≥0)
    (ha : IsStoppingTime 𝓕.rightCont (fun ω => (a ω : WithTop ℝ≥0)))
    (hb : IsStoppingTime 𝓕.rightCont (fun ω => (b ω : WithTop ℝ≥0))) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => (min (a ω) (b ω) : WithTop ℝ≥0)) ∧
    IsStoppingTime 𝓕.rightCont
      (fun ω => (max (a ω) (b ω) : WithTop ℝ≥0)) := by
  constructor
  · intro t
    have hEq :
        {ω : Ω | (min (a ω) (b ω) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
          {ω : Ω | (a ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} ∪
          {ω : Ω | (b ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union, WithTop.coe_le_coe, min_le_iff]
    rw [hEq]
    exact (ha t).union (hb t)
  · intro t
    have hEq :
        {ω : Ω | (max (a ω) (b ω) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
          {ω : Ω | (a ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} ∩
          {ω : Ω | (b ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, WithTop.coe_le_coe, max_le_iff]
    rw [hEq]
    exact (ha t).inter (hb t)
