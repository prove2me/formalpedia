-- Prove2me | solution 1 for AvramDividend.Classical.chat06_prefix_arrival_threshold_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:07:47.486763+00:00
-- url     : https://prove2.me/submissions/fe554354-5d85-4eb8-90e9-887afaed2da7

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- The earlier-arrival count computed from finitely many
prefix partial-sum comparisons is a measurable function of
the infinite sequence encoding that prefix. -/
theorem solution (n : ℕ) (s : ℝ) :
    Measurable (fun z : ℕ → ℝ =>
      ((Finset.range n).filter (fun k =>
        (∑ i ∈ Finset.range (k + 1), z i) ≤ s)).card) := by
  classical
  have hRewrite :
      (fun z : ℕ → ℝ =>
        ((Finset.range n).filter (fun k =>
          (∑ i ∈ Finset.range (k + 1), z i) ≤ s)).card) =
      (fun z : ℕ → ℝ =>
        ∑ k ∈ Finset.range n,
          if (∑ i ∈ Finset.range (k + 1), z i) ≤ s
          then (1 : ℕ) else 0) := by
    funext z
    exact Finset.card_filter _ _
  rw [hRewrite]
  apply Finset.measurable_sum
  intro k hk
  have hSum : Measurable (fun z : ℕ → ℝ =>
      ∑ i ∈ Finset.range (k + 1), z i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hSet : MeasurableSet {z : ℕ → ℝ |
      (∑ i ∈ Finset.range (k + 1), z i) ≤ s} :=
    hSum measurableSet_Iic
  exact Measurable.ite hSet measurable_const measurable_const
