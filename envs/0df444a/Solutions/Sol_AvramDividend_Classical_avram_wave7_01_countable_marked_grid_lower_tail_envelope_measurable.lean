-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_countable_marked_grid_lower_tail_envelope_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:55:59.409691+00:00
-- url     : https://prove2.me/submissions/dc02c976-0910-4bca-927e-eb9579943060

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- The path-coordinate lower-tail grid envelope is measurable. -/
theorem solution
    (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ → ℕ) (grid : ℕ → ℕ → ℝ≥0) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      ⨆ m : ℕ, ⨅ k : ℕ, if m ≤ k then ((((Finset.range (n k)).filter (fun i =>
          Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞)) else ⊤) := by
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
  have hEach (k : ℕ) : Measurable (fun Y : ℝ≥0 → ℝ =>
      (((Finset.range (n k)).filter (fun i =>
        Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞)) :=
    hCast.comp (hFinite k)
  have hTail (m k : ℕ) : Measurable (fun Y : ℝ≥0 → ℝ =>
      if m ≤ k then ((((Finset.range (n k)).filter (fun i =>
          Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞)) else ⊤) := by
    by_cases hmk : m ≤ k
    · simpa only [if_pos hmk] using hEach k
    · simpa only [if_neg hmk] using
        (measurable_const : Measurable (fun _ : ℝ≥0 → ℝ => (⊤ : ℝ≥0∞)))
  exact Measurable.iSup (fun m => Measurable.iInf (fun k => hTail m k))
