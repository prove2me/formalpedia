-- Prove2me | solution 2 for AvramDividend.Classical.record_grid_last_survived_before_finite_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:29:28.114226+00:00
-- url     : https://prove2.me/submissions/8c266f35-998e-4a19-b6e2-b36abe194b0a

import Mathlib.Data.Nat.Basic
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_record_grid_clocks_eventually_ge_horizon
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b h : ℝ) (hh : 0 < h) (T : ℝ≥0) :
    (¬ (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)) <
      (T : ℝ≥0∞)) ∨
    ∃ n : ℕ,
      (⨅ (r : ℝ≥0)
        (_ : b + (n : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) <
        (T : ℝ≥0∞) ∧
      ¬ (⨅ (r : ℝ≥0)
        (_ : b + ((n + 1 : ℕ) : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) <
        (T : ℝ≥0∞) := by
  obtain ⟨N, hN⟩ :=
    firstUpcrossing_record_grid_clocks_eventually_ge_horizon
      X ω T b h hh
  by_cases hfirst :
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)) <
        (T : ℝ≥0∞)
  · right
    by_contra hNo
    have hstep : ∀ n : ℕ,
        (⨅ (r : ℝ≥0)
          (_ : b + (n : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) <
          (T : ℝ≥0∞) →
        (⨅ (r : ℝ≥0)
          (_ : b + ((n + 1 : ℕ) : ℝ) * h < X.X r ω),
          (r : ℝ≥0∞)) < (T : ℝ≥0∞) := by
      intro n hn
      by_contra hn1
      exact hNo ⟨n, hn, hn1⟩
    have hall : ∀ n : ℕ,
        (⨅ (r : ℝ≥0)
          (_ : b + (n : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) <
          (T : ℝ≥0∞) := by
      intro n
      induction n with
      | zero => simpa using hfirst
      | succ n ih => exact hstep n ih
    exact (not_lt_of_ge (hN N le_rfl)) (hall N)
  · left
    exact hfirst
