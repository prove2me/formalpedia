-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:57:52.763529+00:00
-- url     : https://prove2.me/submissions/5865fd8a-9da6-4466-9bee-d3b5e08acd76

import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_bounds
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_mem_finite_grid
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto

set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

open Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Scaled dyadic ceilings approach each finite-horizon time from within the horizon. -/
theorem solution (s T : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) :
    let u : ℕ → ℝ≥0 := fun n =>
      (Nat.ceil (((s / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
        (2 : ℝ≥0) ^ n * T
    (∀ n, s ≤ u n ∧ u n ≤ T) ∧ Tendsto u atTop (𝓝 s) := by
  let r : ℝ≥0 := s / T
  let k : ℕ → ℕ := fun n => Nat.ceil ((r : ℝ) * (2 : ℝ) ^ n)
  let q : ℕ → ℝ≥0 := fun n => (k n : ℝ≥0) / (2 : ℝ≥0) ^ n
  let u : ℕ → ℝ≥0 := fun n => q n * T
  change (∀ n, s ≤ u n ∧ u n ≤ T) ∧ Tendsto u atTop (𝓝 s)
  have hTne : T ≠ 0 := ne_of_gt hT
  have hr : r ≤ 1 := by
    dsimp [r]
    rw [div_le_iff₀ hT]
    simpa using hs
  have heq : r * T = s := by
    dsimp [r]
    exact div_mul_cancel₀ s hTne
  have hlim : Tendsto q atTop (𝓝 r) := by
    exact dyadic_ceiling_nnreal_tendsto r
  constructor
  · intro n
    have hlreal := (dyadic_ceiling_rounding_bounds r n).1
    have hl : r ≤ q n := by
      dsimp [q, k]
      exact_mod_cast hlreal
    have hbound : k n ≤ (2 : ℕ) ^ n := by
      dsimp [k]
      apply (Nat.ceil_le).2
      have hrreal : (r : ℝ) ≤ 1 := by exact_mod_cast hr
      have hc : (2 : ℝ) ^ n = ((2 : ℕ) ^ n : ℝ) := by norm_cast
      calc
        (r : ℝ) * (2 : ℝ) ^ n ≤ (2 : ℝ) ^ n := by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hrreal
              (show (0 : ℝ) ≤ (2 : ℝ) ^ n by positivity))
        _ = ((2 : ℕ) ^ n : ℝ) := hc
      all_goals norm_cast
    have hpow : (k n : ℝ≥0) ≤ (2 : ℝ≥0) ^ n := by
      exact_mod_cast hbound
    have hq : q n ≤ 1 := by
      dsimp [q]
      exact (div_le_one (by positivity)).mpr hpow
    constructor
    · calc
        s = r * T := heq.symm
        _ ≤ q n * T := mul_le_mul_of_nonneg_right hl (by positivity)
        _ = u n := rfl
    · calc
        u n = q n * T := rfl
        _ ≤ 1 * T := mul_le_mul_of_nonneg_right hq (by positivity)
        _ = T := one_mul T
  · simpa only [u, heq] using hlim.mul_const T
