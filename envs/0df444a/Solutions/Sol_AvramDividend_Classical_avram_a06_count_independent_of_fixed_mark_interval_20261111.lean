-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_count_independent_of_fixed_mark_interval_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:56:37.370394+00:00
-- url     : https://prove2.me/submissions/fad73fa3-74aa-4b10-9b23-459baabf4bff

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Ω → Fin (n + 1) → ℕ) (Y : Ω → ℕ → ℝ)
    (hSeparate : IndepFun N Y P) (a b : ℕ) :
    IndepFun N (fun ω => ∑ j ∈ Finset.Ico a b, Y ω j) P := by
  have hsum : Measurable
      (fun ys : ℕ → ℝ => ∑ j ∈ Finset.Ico a b, ys j) :=
    Finset.measurable_sum (Finset.Ico a b)
      (fun j _ => measurable_pi_apply j)
  have hcomp := hSeparate.comp measurable_id hsum
  simpa [Function.comp_def] using hcomp
