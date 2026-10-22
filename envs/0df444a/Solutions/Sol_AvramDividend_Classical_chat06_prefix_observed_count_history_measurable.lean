-- Prove2me | solution 1 for AvramDividend.Classical.chat06_prefix_observed_count_history_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:16:08.534151+00:00
-- url     : https://prove2.me/submissions/38a11ec0-0171-48cf-8043-4c188124c97a

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- All observed earlier counts, indexed by the complete interval
up to the observation clock, form a measurable path-valued
function of the truncated interarrival prefix. -/
theorem solution (n : ℕ) (clock : ℝ) :
    Measurable (fun z : ℕ → ℝ =>
      fun s : Set.Iic clock =>
        ((Finset.range n).filter (fun k =>
          (∑ i ∈ Finset.range (k + 1), z i) ≤ (s : ℝ))).card) := by
  classical
  apply measurable_pi_iff.mpr
  intro s
  have hRewrite :
      (fun z : ℕ → ℝ =>
        ((Finset.range n).filter (fun k =>
          (∑ i ∈ Finset.range (k + 1), z i) ≤ (s : ℝ))).card) =
      (fun z : ℕ → ℝ =>
        ∑ k ∈ Finset.range n,
          if (∑ i ∈ Finset.range (k + 1), z i) ≤ (s : ℝ)
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
      (∑ i ∈ Finset.range (k + 1), z i) ≤ (s : ℝ)} :=
    hSum measurableSet_Iic
  exact Measurable.ite hSet measurable_const measurable_const
