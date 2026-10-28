-- Prove2me | solution 1 for AvramDividend.Classical.variable_finite_marks_sum_measurable_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:28:21.064408+00:00
-- url     : https://prove2.me/submissions/b10e5473-3900-4c58-8a75-4a85bcec8544

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- The sum of the first n measurable marks is jointly measurable in
the count n and the entire sequence of marks. -/
theorem solution
    {E : Type*} [MeasurableSpace E]
    (f : E → ℝ) (hf : Measurable f) :
    Measurable (fun p : ℕ × (ℕ → E) =>
      ∑ n ∈ Finset.range p.1, f (p.2 n)) := by
  have hterm (n : ℕ) :
      Measurable (fun p : ℕ × (ℕ → E) =>
        if n < p.1 then f (p.2 n) else 0) := by
    have hcond : MeasurableSet {p : ℕ × (ℕ → E) | n < p.1} := by
      exact measurableSet_Ioi.preimage
        (measurable_fst : Measurable (fun p : ℕ × (ℕ → E) => p.1))
    have hmark :
        Measurable (fun p : ℕ × (ℕ → E) => f (p.2 n)) := by
      fun_prop
    exact Measurable.ite hcond hmark measurable_const
  have hsum :
      Measurable (fun p : ℕ × (ℕ → E) =>
        ∑' n : ℕ, if n < p.1 then f (p.2 n) else 0) :=
    Measurable.tsum hterm
  have heq (p : ℕ × (ℕ → E)) :
      (∑' n : ℕ, if n < p.1 then f (p.2 n) else 0) =
        ∑ n ∈ Finset.range p.1, f (p.2 n) := by
    rw [tsum_eq_sum (s := Finset.range p.1) (by
      intro n hn
      have hn' : ¬ n < p.1 := by simpa using hn
      simp [hn'])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [Finset.mem_range.mp hn]
  simpa only [heq] using hsum
