-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_adjacent_independent_interval_charfun_concat_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:23:29.349864+00:00
-- url     : https://prove2.me/submissions/5f50264c-16e0-48f7-9944-ea1296796b85

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

/-- Concatenating independent adjacent blocks multiplies their Fourier laws. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ j, Measurable (Y j))
    (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (hInd : IndepFun
      (fun ω => ∑ j ∈ Finset.Ico a b, Y j ω)
      (fun ω => ∑ j ∈ Finset.Ico b c, Y j ω) P)
    (t : ℝ) :
    MeasureTheory.charFun
      (Measure.map (fun ω => ∑ j ∈ Finset.Ico a c, Y j ω) P) t =
    MeasureTheory.charFun
      (Measure.map (fun ω => ∑ j ∈ Finset.Ico a b, Y j ω) P) t *
    MeasureTheory.charFun
      (Measure.map (fun ω => ∑ j ∈ Finset.Ico b c, Y j ω) P) t := by
  have hu : Finset.Ico a c = Finset.Ico a b ∪ Finset.Ico b c := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ico a b) (Finset.Ico b c) := by
    apply Finset.disjoint_left.mpr
    intro j hj1 hj2
    simp only [Finset.mem_Ico] at hj1 hj2
    omega
  have hSplit (ω : Ω) :
      (∑ j ∈ Finset.Ico a c, Y j ω) =
        (∑ j ∈ Finset.Ico a b, Y j ω) +
        (∑ j ∈ Finset.Ico b c, Y j ω) := by
    rw [hu, Finset.sum_union hd]
  have hXA : Measurable (fun ω : Ω => ∑ j ∈ Finset.Ico a b, Y j ω) :=
    Finset.measurable_sum _ (fun j hj => hY j)
  have hXB : Measurable (fun ω : Ω => ∑ j ∈ Finset.Ico b c, Y j ω) :=
    Finset.measurable_sum _ (fun j hj => hY j)
  have hEq : (fun ω : Ω => ∑ j ∈ Finset.Ico a c, Y j ω) =
      (fun ω : Ω =>
        (∑ j ∈ Finset.Ico a b, Y j ω) +
        (∑ j ∈ Finset.Ico b c, Y j ω)) := funext hSplit
  rw [hEq]
  exact congrFun (ProbabilityTheory.IndepFun.charFun_map_fun_add_eq_mul
    hXA.aemeasurable hXB.aemeasurable hInd) t
