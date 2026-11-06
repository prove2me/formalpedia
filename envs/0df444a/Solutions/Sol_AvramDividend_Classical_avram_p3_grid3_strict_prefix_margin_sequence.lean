-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_strict_prefix_margin_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:50:26.996508+00:00
-- url     : https://prove2.me/submissions/b0e113df-51e3-4e72-91e2-a2b8c3adcdca

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
noncomputable section

/-- A strictly positive physical cash-prefix margin shrinking to zero. -/
theorem solution
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    (∀ n, 0 < δ n) ∧
    (∀ n, δ n ≤ T) ∧
    Antitone δ ∧
    Filter.Tendsto δ Filter.atTop (nhds 0) := by
  dsimp
  constructor
  · intro n
    exact div_pos hT (by positivity)
  constructor
  · intro n
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith [mul_nonneg (le_of_lt hT) hn]
  constructor
  · intro a b hab
    have hr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    apply (div_le_div_iff₀ (by positivity : 0 < (b : ℝ) + 2)
      (by positivity : 0 < (a : ℝ) + 2)).2
    nlinarith [mul_nonneg (le_of_lt hT) (sub_nonneg.mpr hr)]
  · have h := (tendsto_const_div_atTop_nhds_zero_nat T).comp
        (Filter.tendsto_add_atTop_nat 2)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h
