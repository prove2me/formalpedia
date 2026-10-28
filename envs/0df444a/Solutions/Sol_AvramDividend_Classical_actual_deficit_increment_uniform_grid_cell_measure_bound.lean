-- Prove2me | solution 1 for AvramDividend.Classical.actual_deficit_increment_uniform_grid_cell_measure_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:57:12.214861+00:00
-- url     : https://prove2.me/submissions/850704ad-e8f5-4277-9ffa-5a910371b7f7

import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Identical grid-cell lengths inherit the actual Lévy deficit's one-time event law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (N : ℕ) (ts : ℕ → ℝ≥0) (δ : ℝ≥0)
    (b : ℝ) (u : ℝ≥0∞)
    (hStep : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hSpacing : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ)
    (hOne : P {ω : Ω |
      0 < X.drift * (δ : ℝ) - X.X δ ω ∧
      X.drift * (δ : ℝ) - X.X δ ω ≤ b} ≤ u) :
    ∀ k : ℕ, k < N →
      P {ω : Ω |
        0 < (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
          (X.drift * (ts k : ℝ) - X.X (ts k) ω) ∧
        (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
          (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤ b} ≤ u := by
  intro k hk
  have hIdent :=
    actual_levy_drift_deficit_stationary_increment_law
      X (ts k) (ts (k + 1)) (hStep k hk)
  have hSet : MeasurableSet {z : ℝ | 0 < z ∧ z ≤ b} := by
    exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)
  have hMass := hIdent.measure_mem_eq hSet
  have hEq :
      P {ω : Ω |
        0 < (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
          (X.drift * (ts k : ℝ) - X.X (ts k) ω) ∧
        (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
          (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤ b} =
      P {ω : Ω |
        0 < X.drift * ((ts (k + 1) - ts k : ℝ≥0) : ℝ) -
          X.X (ts (k + 1) - ts k) ω ∧
        X.drift * ((ts (k + 1) - ts k : ℝ≥0) : ℝ) -
          X.X (ts (k + 1) - ts k) ω ≤ b} := by
    simpa only [Set.preimage, Set.mem_setOf_eq] using hMass
  rw [hEq, hSpacing k hk]
  exact hOne
