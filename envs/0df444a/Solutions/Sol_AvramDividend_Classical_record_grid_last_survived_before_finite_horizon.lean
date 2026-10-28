-- Prove2me | solution 1 for AvramDividend.Classical.record_grid_last_survived_before_finite_horizon
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:29:09.319603+00:00
-- url     : https://prove2.me/submissions/afca67f4-0a7a-4ab9-a768-09ba26e44fae

import Mathlib.Data.Nat.Basic
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_record_grid_clocks_eventually_ge_horizon

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
  classical
  obtain ⟨N, hN⟩ := AvramDividend.Classical.firstUpcrossing_record_grid_clocks_eventually_ge_horizon X ω T b h hh
  by_cases h0 : (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)) < (T : ℝ≥0∞)
  · right
    have hex : ∃ n : ℕ, ¬ (⨅ (r : ℝ≥0) (_ : b + (n : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < (T : ℝ≥0∞) :=
      ⟨N, not_lt.2 (hN N le_rfl)⟩
    have hm := Nat.find_spec hex
    have hm0 : Nat.find hex ≠ 0 := by
      intro e; rw [e] at hm; apply hm; simpa using h0
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    refine ⟨k, ?_, ?_⟩
    · have := Nat.find_min hex (show k < Nat.find hex by omega)
      exact not_not.1 this
    · have e : Nat.find hex = k + 1 := hk
      rw [e] at hm; exact hm
  · left; exact h0
