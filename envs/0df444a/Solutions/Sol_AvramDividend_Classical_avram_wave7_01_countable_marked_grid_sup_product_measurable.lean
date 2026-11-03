-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_countable_marked_grid_sup_product_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:07:26.791841+00:00
-- url     : https://prove2.me/submissions/4c27841c-2b54-484e-9c4f-251dabceb48e

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ → ℕ) (grid : ℕ → ℕ → ℝ≥0) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      ⨆ k : ℕ, (((Finset.range (n k)).filter (fun i =>
        Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞)) := by
  classical
  have hFinite (k : ℕ) : Measurable (fun Y : ℝ≥0 → ℝ =>
      ((Finset.range (n k)).filter (fun i =>
        Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card) := by
    have hp (i : ℕ) : MeasurableSet {Y : ℝ≥0 → ℝ |
        Y (grid k (i + 1)) - Y (grid k i) ∈ B} := by
      exact hB.preimage
        ((measurable_pi_apply (grid k (i + 1))).sub
          (measurable_pi_apply (grid k i)))
    have hSum : Measurable (fun Y : ℝ≥0 → ℝ =>
        ∑ i ∈ Finset.range (n k),
          if Y (grid k (i + 1)) - Y (grid k i) ∈ B then (1 : ℕ) else 0) := by
      apply Finset.measurable_sum
      intro i hi
      exact Measurable.ite (hp i) measurable_const measurable_const
    have hEq :
        (fun Y : ℝ≥0 → ℝ =>
          ((Finset.range (n k)).filter (fun i =>
            Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card) =
        (fun Y : ℝ≥0 → ℝ =>
          ∑ i ∈ Finset.range (n k),
            if Y (grid k (i + 1)) - Y (grid k i) ∈ B then (1 : ℕ) else 0) := by
      funext Y
      exact Finset.card_filter
        (fun i => Y (grid k (i + 1)) - Y (grid k i) ∈ B)
        (Finset.range (n k))
    rw [hEq]
    exact hSum
  have hCast : Measurable (fun q : ℕ => (q : ℝ≥0∞)) :=
    measurable_of_countable _
  exact Measurable.iSup (fun k : ℕ => hCast.comp (hFinite k))
