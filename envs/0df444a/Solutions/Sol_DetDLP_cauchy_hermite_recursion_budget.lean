-- Prove2me | solution 1 for DetDLP.cauchy_hermite_recursion_budget
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:23:55.324114+00:00
-- url     : https://prove2.me/submissions/056669b6-7012-4022-838c-be2329782e6a

import Mathlib

set_option autoImplicit false

private lemma one_eight_div_sqrt_half_pow (d : ℕ) :
    ((1 : ℝ) / 8) ^ d / Real.sqrt (((1 : ℝ) / 2) ^ d) ≤ ((1 : ℝ) / 4) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hsqrt_step : Real.sqrt (((1 : ℝ) / 2) ^ (d + 1)) =
        Real.sqrt (((1 : ℝ) / 2) ^ d) * Real.sqrt ((1 : ℝ) / 2) := by
      rw [pow_succ, Real.sqrt_mul (by positivity)]
    have hfrac : (1 : ℝ) / 8 / Real.sqrt ((1 : ℝ) / 2) ≤ 1 / 4 := by
      have hs_pos : 0 < Real.sqrt ((1 : ℝ) / 2) := Real.sqrt_pos.mpr (by norm_num)
      rw [div_le_div_iff₀ hs_pos (by norm_num)]
      have hsq : ((1 : ℝ) / 2) ^ 2 ≤ (1 : ℝ) / 2 := by norm_num
      have hle : (1 : ℝ) / 2 ≤ Real.sqrt ((1 : ℝ) / 2) := Real.le_sqrt_of_sq_le hsq
      linarith
    have hih_nn : 0 ≤ ((1 : ℝ) / 8) ^ d / Real.sqrt (((1 : ℝ) / 2) ^ d) := by positivity
    rw [pow_succ ((1 : ℝ) / 8) d, pow_succ ((1 : ℝ) / 4) d, hsqrt_step]
    have hsplit : ((1 : ℝ) / 8) ^ d * (1 / 8) /
        (Real.sqrt (((1 : ℝ) / 2) ^ d) * Real.sqrt (1 / 2)) =
        (((1 : ℝ) / 8) ^ d / Real.sqrt (((1 : ℝ) / 2) ^ d)) *
        ((1 / 8) / Real.sqrt (1 / 2)) := by
      ring
    rw [hsplit]
    exact mul_le_mul ih hfrac (by positivity) (by positivity)

theorem solution :
    (∀ (D : ℕ) (β ρ : ℝ), 0 ≤ β → 0 < ρ →
      ∑ d ∈ Finset.range (D + 1),
        (β * ((1 : ℝ) / 8) ^ d) / Real.sqrt (ρ * ((1 : ℝ) / 2) ^ d) ≤
        (4 / 3 : ℝ) * (β / Real.sqrt ρ)) ∧
    (∀ (D : ℕ) (ε ρ : ℝ), 0 ≤ ε → 0 ≤ ρ →
      2 * (∑ j ∈ Finset.range (D + 1), (Nat.floor (ε * ρ / (2 : ℝ) ^ j) : ℝ)) ≤
        4 * ε * ρ) ∧
    (∀ M : ℕ, 1 ≤ M →
      3 * M / 32 < M / 8 + 1 ∧ (3 : ℝ) * (M : ℝ) / 32 < (M : ℝ) / 8) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: Geometric decay ∑_{d=0}^D (β / 8^d) / √(ρ / 2^d) ≤ (4/3) (β / √ρ)
    intro D β ρ hβ hρ
    have hterm : ∀ d : ℕ,
        (β * ((1 : ℝ) / 8) ^ d) / Real.sqrt (ρ * ((1 : ℝ) / 2) ^ d) ≤
        (β / Real.sqrt ρ) * ((1 : ℝ) / 4) ^ d := by
      intro d
      rw [Real.sqrt_mul (le_of_lt hρ)]
      have hrew : (β * ((1 : ℝ) / 8) ^ d) / (Real.sqrt ρ * Real.sqrt (((1 : ℝ) / 2) ^ d)) =
          (β / Real.sqrt ρ) * (((1 : ℝ) / 8) ^ d / Real.sqrt (((1 : ℝ) / 2) ^ d)) := by
        ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_left (one_eight_div_sqrt_half_pow d) (by positivity)
    calc ∑ d ∈ Finset.range (D + 1),
            (β * ((1 : ℝ) / 8) ^ d) / Real.sqrt (ρ * ((1 : ℝ) / 2) ^ d)
        ≤ ∑ d ∈ Finset.range (D + 1), (β / Real.sqrt ρ) * ((1 : ℝ) / 4) ^ d :=
          Finset.sum_le_sum fun d _ => hterm d
      _ = (β / Real.sqrt ρ) * ∑ d ∈ Finset.range (D + 1), ((1 : ℝ) / 4) ^ d := by
          rw [← Finset.mul_sum]
      _ = (β / Real.sqrt ρ) * ((((1 : ℝ) / 4) ^ (D + 1) - 1) / ((1 : ℝ) / 4 - 1)) := by
          rw [geom_sum_eq (by norm_num)]
      _ ≤ (β / Real.sqrt ρ) * (4 / 3 : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hpow : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ (D + 1) := by positivity
          have hid : (((1 : ℝ) / 4) ^ (D + 1) - 1) / ((1 : ℝ) / 4 - 1) =
              (1 - ((1 : ℝ) / 4) ^ (D + 1)) * (4 / 3 : ℝ) := by ring
          rw [hid]
          nlinarith
      _ = (4 / 3 : ℝ) * (β / Real.sqrt ρ) := by ring
  · -- Part 2: Cumulative depth bound 2 ∑_{j=0}^D ⌊ε ρ / 2^j⌋ ≤ 4 ε ρ
    intro D ε ρ hε hρ
    have hfl : ∀ j : ℕ, (Nat.floor (ε * ρ / (2 : ℝ) ^ j) : ℝ) ≤ (ε * ρ) * ((1 : ℝ) / 2) ^ j := by
      intro j
      have h1 := Nat.floor_le (show 0 ≤ ε * ρ / (2 : ℝ) ^ j by positivity)
      have h2 : ε * ρ / (2 : ℝ) ^ j = (ε * ρ) * ((1 : ℝ) / 2) ^ j := by
        rw [one_div, inv_pow, div_eq_mul_inv]
      linarith
    calc 2 * (∑ j ∈ Finset.range (D + 1), (Nat.floor (ε * ρ / (2 : ℝ) ^ j) : ℝ))
        ≤ 2 * (∑ j ∈ Finset.range (D + 1), (ε * ρ) * ((1 : ℝ) / 2) ^ j) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hfl j) (by norm_num)
      _ = 2 * (ε * ρ) * ∑ j ∈ Finset.range (D + 1), ((1 : ℝ) / 2) ^ j := by
          rw [← Finset.mul_sum]; ring
      _ = 2 * (ε * ρ) * ((((1 : ℝ) / 2) ^ (D + 1) - 1) / ((1 : ℝ) / 2 - 1)) := by
          rw [geom_sum_eq (by norm_num)]
      _ ≤ 2 * (ε * ρ) * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hpow : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (D + 1) := by positivity
          have hid : (((1 : ℝ) / 2) ^ (D + 1) - 1) / ((1 : ℝ) / 2 - 1) =
              2 * (1 - ((1 : ℝ) / 2) ^ (D + 1)) := by ring
          rw [hid]
          linarith
      _ = 4 * ε * ρ := by ring
  · -- Part 3: Edge shrinkage 3M/32 < M/8
    intro M hM
    refine ⟨by omega, ?_⟩
    have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
