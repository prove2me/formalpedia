-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_partial_sum_aestronglymeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:20:23.210988+00:00
-- url     : https://prove2.me/submissions/c96607ab-af9b-4de9-bf5b-f36a13654a22

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Algebra.BigOperators.Pi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Integrable Neumann terms have measurable finite-sum convolution products. -/
theorem solution
    (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hI : ∀ m : ℕ, ∀ x : ℝ, ∀ i ∈ Finset.range (m + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume) :
    ∀ x : ℝ, ∀ n : ℕ, AEStronglyMeasurable
      (fun s : ℝ => B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s)
      (volume.restrict (Ioc (0 : ℝ) x)) := by
  intro x n
  have hterm : ∀ i ∈ Finset.range (n + 1),
      AEStronglyMeasurable (fun s : ℝ => B (x - s) * Q i s)
        (volume.restrict (Ioc (0 : ℝ) x)) := by
    intro i hi
    exact (hI n x i hi).aestronglyMeasurable
  have hsum := Finset.aestronglyMeasurable_fun_sum
    (Finset.range (n + 1)) hterm
  simpa only [Finset.sum_apply, Finset.mul_sum] using hsum
