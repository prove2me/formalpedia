-- Prove2me | solution 1 for Esgk.distinct_distances_deficiency_threshold_alternatives
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-20T04:59:41.179996+00:00
-- url     : https://prove2.me/submissions/c689db38-569e-4b97-b341-0ec04cd82c5f

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Theorems.Thm_Esgk_distinct_distances_one_fourth_excess
import Definitions.Def_Esgk_Foundation
import Mathlib

/-!
# Five threshold branches from the fourth-root excess

Write `3 D = (n - 1) + σ`. The fourth-root excess gives `σ + 1 ≥ 3 c n^(1/4)`,
so `(σ + 1)^4 ≥ (3c)^4 n`, and a fixed natural number `A ≥ 1/(3c)^4` gives
`n ≤ A (σ + 1)^5`. This is the last of the five branches, with `T = 1` and
`C = A`.
-/

open EuclideanGeometry Filter Esgk

/-- The quintic deficiency bound, derived from the fourth-root excess. -/
private theorem quintic_nat_bound :
    ∃ A : ℕ, 0 < A ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          ∃ σ : ℕ,
            (n - 1) + σ = 3 * distinctDistances (Config.toFinset p) ∧
            n ≤ A * (σ + 1) ^ 5 := by
  obtain ⟨c, hc, h⟩ := distinct_distances_one_fourth_excess
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (3 * c) ^ 4 := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; positivity
  refine ⟨⌈1 / k⌉₊, Nat.ceil_pos.mpr (by positivity), ?_⟩
  filter_upwards [h] with n hn p hp hgp
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · refine ⟨3 * distinctDistances (Config.toFinset p), by omega, ?_⟩
    subst h0
    exact Nat.zero_le _
  have hmain := hn p hp hgp
  obtain ⟨D, hD⟩ : ∃ D, D = distinctDistances (Config.toFinset p) := ⟨_, rfl⟩
  rw [← hD] at hmain ⊢
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.rpow (n : ℝ) (1 / 4 : ℝ) := ⟨_, rfl⟩
  rw [← hx] at hmain
  have hx0 : 0 ≤ x := by rw [hx]; exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hx4 : x ^ 4 = (n : ℝ) := by
    rw [hx, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by norm_num)
  have hnD : n ≤ 3 * D := by
    have : (n : ℝ) ≤ 3 * (D : ℝ) := by nlinarith [mul_nonneg hc.le hx0]
    exact_mod_cast this
  refine ⟨3 * D - (n - 1), by omega, ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = 3 * D - (n - 1) + 1 := ⟨_, rfl⟩
  rw [← hs]
  have hsn : s + n = 3 * D + 2 := by omega
  have hsR : (s : ℝ) = 3 * (D : ℝ) - n + 2 := by
    have h' : (s : ℝ) + n = 3 * (D : ℝ) + 2 := by exact_mod_cast hsn
    linarith
  have hs3 : 3 * c * x ≤ (s : ℝ) := by rw [hsR]; nlinarith
  have hs1 : (1 : ℝ) ≤ s := by
    have : 1 ≤ s := by omega
    exact_mod_cast this
  have h4 : k * n ≤ (s : ℝ) ^ 4 := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * c * x) hs3 4
    have heq : (3 * c * x) ^ 4 = k * n := by rw [mul_pow, hx4, hk]
    linarith
  have h5 : (s : ℝ) ^ 4 ≤ (s : ℝ) ^ 5 := pow_le_pow_right₀ hs1 (by norm_num)
  have hA : 1 / k ≤ (⌈1 / k⌉₊ : ℝ) := Nat.le_ceil _
  have hAk : 1 ≤ (⌈1 / k⌉₊ : ℝ) * k := by
    have := mul_le_mul_of_nonneg_right hA hk0.le
    rwa [div_mul_cancel₀ (1 : ℝ) hk0.ne'] at this
  have hreal : (n : ℝ) ≤ (⌈1 / k⌉₊ : ℝ) * (s : ℝ) ^ 5 := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc (n : ℝ) ≤ (⌈1 / k⌉₊ : ℝ) * k * n := by nlinarith
      _ = (⌈1 / k⌉₊ : ℝ) * (k * n) := by ring
      _ ≤ (⌈1 / k⌉₊ : ℝ) * (s : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_left (h4.trans h5) (Nat.cast_nonneg _)
  exact_mod_cast hreal

theorem solution :
    ∃ T C : ℕ, 0 < T ∧ 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          ∃ σ : ℕ,
            (n - 1) + σ = 3 * distinctDistances (Config.toFinset p) ∧
            let s := σ + 1
            n ≤ 3 * s ∨ n ≤ s ^ 2 ∨ n ≤ s ∨
              n ^ 2 < 128 * T * s ^ 7 ∨ n ≤ 32 * C * s ^ 5 := by
  obtain ⟨A, hA, h⟩ := quintic_nat_bound
  refine ⟨1, A, Nat.one_pos, hA, ?_⟩
  filter_upwards [h] with n hn p hp hgp
  obtain ⟨σ, hσ, hle⟩ := hn p hp hgp
  refine ⟨σ, hσ, ?_⟩
  intro s
  right; right; right; right
  calc n ≤ A * (σ + 1) ^ 5 := hle
    _ ≤ 32 * A * (σ + 1) ^ 5 := by
      rw [mul_assoc]
      exact Nat.le_mul_of_pos_left _ (by norm_num)
