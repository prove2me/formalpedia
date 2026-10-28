-- Prove2me | solution 1 for AvramDividend.Classical.stopped_record_grid_last_survived_or_no_initial_hit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:59:40.594001+00:00
-- url     : https://prove2.me/submissions/077da1b6-bed3-41d3-8597-827a70eb1b97

import Mathlib.Data.Nat.Basic
import Theorems.Thm_AvramDividend_Classical_chat08_named_stopped_grid_no_late_hit_of_finite_ruin
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
    (a b h : ℝ) (hh : 0 < h) (τ : ℝ≥0)
    (hτ : barrierRuinTime X a ω = (τ : ℝ≥0∞)) :
    (¬ twoSidedExitUpTime X b ω < barrierRuinTime X a ω) ∨
    ∃ n : ℕ,
      twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
        barrierRuinTime X a ω ∧
      ¬ twoSidedExitUpTime X (b + ((n + 1 : ℕ) : ℝ) * h) ω <
        barrierRuinTime X a ω := by
  obtain ⟨N, hN⟩ :=
    chat08_named_stopped_grid_no_late_hit_of_finite_ruin
      X ω a b h hh τ hτ
  by_cases hfirst :
      twoSidedExitUpTime X b ω < barrierRuinTime X a ω
  · right
    by_contra hNo
    have hstep : ∀ n : ℕ,
        twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
          barrierRuinTime X a ω →
        twoSidedExitUpTime X (b + ((n + 1 : ℕ) : ℝ) * h) ω <
          barrierRuinTime X a ω := by
      intro n hn
      by_contra hn1
      exact hNo ⟨n, hn, hn1⟩
    have hall : ∀ n : ℕ,
        twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
          barrierRuinTime X a ω := by
      intro n
      induction n with
      | zero => simpa using hfirst
      | succ n ih => exact hstep n ih
    exact (hN N le_rfl) (hall N)
  · left
    exact hfirst
